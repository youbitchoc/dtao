#define _GNU_SOURCE
#include <ctype.h>
#include <errno.h>
#include <fcft/fcft.h>
#include <fcntl.h>
#include <limits.h>
#include <pixman.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/select.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>
#include <wayland-client.h>
#include "utf8.h"
#include "wlr-layer-shell-unstable-v1-protocol.h"
#include "xdg-shell-protocol.h"

#define BARF(fmt, ...)		do { fprintf(stderr, fmt "\n", ##__VA_ARGS__); exit(EXIT_FAILURE); } while (0)
#define EBARF(fmt, ...)		BARF(fmt ": %s", ##__VA_ARGS__, strerror(errno))
#define MIN(a, b)               ((a) < (b) ? (a) : (b))
#define MAX(a, b)               ((a) > (b) ? (a) : (b))

#define PROGRAM "dtao"
#define VERSION "0.1"
#define COPYRIGHT "copyright 2021 Devin J. Pohly and dtao team"
#define USAGE \
	"usage: dtao [-v] [-p seconds] [-m <v|h>] [-ta <l|c|r>] [-sa <l|c|r>]\n" \
	"            [-w <pixel>] [-h <pixel>] [-tw <pixel>] [-l <lines>] [-u]\n" \
	"            [-e <string>] [-fn <font>] [-bg <color>] [-fg <color>]\n" \
	"            [-expand <l|c|r>] [-z [-z]] [-xs <screen>]"

/* Includes the newline character */
#define MAX_LINE_LEN 8192
#define MAX_CLICKABLES 64
#define SCROLL_THRESHOLD 400

enum align { ALIGN_C, ALIGN_L, ALIGN_R };

static struct wl_display *display;
static struct wl_compositor *compositor;
static struct wl_shm *shm;
static struct zwlr_layer_shell_v1 *layer_shell;

static struct zwlr_layer_surface_v1 *layer_surface;
static struct wl_output *wl_output;
static struct wl_surface *wl_surface;

static struct wl_seat *wl_seat;
static struct wl_pointer *wl_pointer;

static int32_t output = -1;
static char *output_name = NULL;

static uint32_t width, height, titlewidth;
static uint32_t stride, bufsize;
static int lines;
static int persist = 0;
static bool unified;
static int exclusive_zone = -1;
static enum align titlealign, subalign;
static bool expand;
static bool run_display = true;
static bool eof_stdin = false;

static uint32_t savedx = 0;

static struct fcft_font *font;
static char line[MAX_LINE_LEN];
static char lastline[MAX_LINE_LEN];
static int linerem;
static bool eat_line = false;
static pixman_color_t
	bgcolor = {
		.red = 0x1111,
		.green = 0x1111,
		.blue = 0x1111,
		.alpha = 0xffff,
	},
	fgcolor = {
		.red = 0xb3b3,
		.green = 0xb3b3,
		.blue = 0xb3b3,
		.alpha = 0xffff,
	};

struct clickable {
	uint32_t x1, y1, x2, y2;
	uint8_t btn;
	char *cmd;
};

static int clickies = 0;
static struct clickable clickables[MAX_CLICKABLES];
static int clickstack[MAX_CLICKABLES];
static int clickstacktop;

static int64_t cur_axis = -1;
static wl_fixed_t cur_scroll = 0;
static wl_fixed_t cur_scrollcarry = 0;

static void
wl_buffer_release(void *data, struct wl_buffer *wl_buffer)
{
	/* Sent by the compositor when it's no longer using this buffer */
	wl_buffer_destroy(wl_buffer);
}

static const struct wl_buffer_listener wl_buffer_listener = {
	.release = wl_buffer_release,
};

/* Shared memory support function adapted from [wayland-book] */
static int
allocate_shm_file(size_t size)
{
	int fd = memfd_create("surface", MFD_CLOEXEC);
	if (fd < 0)
		return -1;
	int ret;
	do {
		ret = ftruncate(fd, size);
	} while (ret < 0 && errno == EINTR);
	if (ret < 0) {
		close(fd);
		return -1;
	}
	return fd;
}

/* Color parsing logic adapted from [sway] */
static int
parse_color(const char *str, pixman_color_t *clr)
{
	if (*str == '#')
		str++;
	int len = strlen(str);

	// Disallows "0x" prefix that strtoul would ignore
	if ((len != 6 && len != 8) || !isxdigit(str[0]) || !isxdigit(str[1]))
		return 1;

	char *ptr;
	uint32_t parsed = strtoul(str, &ptr, 16);
	if (*ptr)
		return 1;

	if (len == 8) {
		clr->alpha = (parsed & 0xff) * 0x101;
		parsed >>= 8;
	} else {
		clr->alpha = 0xffff;
	}
	clr->red =   ((parsed >> 16) & 0xff) * 0x101;
	clr->green = ((parsed >>  8) & 0xff) * 0x101;
	clr->blue =  ((parsed >>  0) & 0xff) * 0x101;
	return 0;
}

static int
parse_movement_arg(const char *str, uint32_t max)
{
	if (!str)
		return 0;

	if (*str == '-')
		return -(parse_movement_arg (++str, max));

	if (*str == 'w')
		return atoi(++str) * max / 100;

	if (*str == 'd')
		return atoi(++str) * font->descent / 100;

	if (*str == 'a')
		return atoi(++str) * font->ascent / 100;

	return atoi(str);
}

static int
parse_movement (char *str, uint32_t *xpos, uint32_t *ypos, uint32_t xoffset, uint32_t yoffset)
{
	char *xarg = str;
	char *yarg;

	if (!*str) {
		*ypos = (height + font->ascent - font->descent) / 2;
	} else if (!(yarg = strchr(str, ';'))) {
		if (*str == '_') {
			if (!strcmp(str, "_LEFT")) {
				*xpos = 0;
			} else if (!strcmp(str, "_RIGHT")) {
				*xpos = width;
			} else if (!strcmp(str, "_CENTER")) {
				*xpos = width/2;
			} else if (!strcmp(str, "_TOP")) {
				*ypos = 0;
			} else if (!strcmp(str, "_BOTTOM")) {
				*ypos = height;
			} else {
				return 1;
			}
		} else {
			*xpos = parse_movement_arg (str, width) + xoffset;
		}
	} else if (*str == ';') {
		*ypos = parse_movement_arg (++str, height) + yoffset;
	} else {
		*yarg++ = '\0';	
		*ypos = parse_movement_arg (yarg, height) + yoffset;
		*xpos = parse_movement_arg (xarg, width) + xoffset;
		*--yarg = ';';
	}

	if (*xpos > width)
		*xpos = width;

	if (*ypos > height)
		*ypos = height;

	return 0;
}

static int
parse_clickable(char *str, struct clickable *c, uint32_t xpos, uint32_t ypos)
{
	c->x1 = xpos;
	c->y1 = 0;
	c->btn = 0;

	for (; *str && *str != ','; str++)
		if (isdigit(*str))
			c->btn = c->btn*10 + (*str - '0');

	if (!*str)
		return 1;

	free(c->cmd);
	c->cmd = strdup(str + 1);

	if (!c->cmd)
		EBARF("malloc: ");

	return 0;
}

static char *
handle_cmd(char *cmd, pixman_color_t *bg, pixman_color_t *fg, uint32_t *xpos, uint32_t *ypos)
{
	char *arg, *end;

	if (!(arg = strchr(cmd, '(')) || !(end = strchr(arg + 1, ')')))
		return cmd;

	*arg++ = '\0';
	*end = '\0';

	if (!strcmp(cmd, "bg")) {
		if (!*arg) {
			*bg = bgcolor;
		} else if (parse_color(arg, bg)) {
			fprintf(stderr, "Bad color string \"%s\"\n", arg);
		}
	} else if (!strcmp(cmd, "fg")) {
		if (!*arg) {
			*fg = fgcolor;
		} else if (parse_color(arg, fg)) {
			fprintf(stderr, "Bad color string \"%s\"\n", arg);
		}
	} else if (!strcmp(cmd, "pa")) {
		if (parse_movement (arg, xpos, ypos, 0, 0))
			fprintf(stderr, "Invalid absolute position argument \"%s\"\n", arg);
	} else if (!strcmp(cmd, "p")) {
		if (parse_movement (arg, xpos, ypos, *xpos, *ypos))
			fprintf(stderr, "Invalid relative position argument \"%s\"\n", arg);
	} else if (!strcmp(cmd, "sx")) {
		savedx = *xpos;
	} else if (!strcmp(cmd, "rx")) {
		*xpos = savedx;
	} else if (!strcmp(cmd, "ca")) {
		if (!*arg) {
			if (clickstacktop < 1)
				BARF("Bad click areas");
			clickstacktop--;
			clickables[clickstack[clickstacktop]].x2 = *xpos;
			clickables[clickstack[clickstacktop]].y2 = height;
		} else {
			clickstack[clickstacktop] = clickies++;
			if (parse_clickable(arg,
					    &clickables[clickstack[clickstacktop]],
					    *xpos, *ypos))
				fprintf(stderr, "Bad click area \"%s\"\n", arg);
			else
				clickstacktop++;
		}
	} else {
		fprintf(stderr, "Unrecognized command \"%s\"\n", cmd);
	}

	/* Restore string for later redraws */
	*--arg = '(';
	*end = ')';
	return end;
}

static struct wl_buffer *
draw_frame(char *text)
{
	/* Allocate buffer to be attached to the surface */
	int fd = allocate_shm_file(bufsize);
	if (fd == -1)
		return NULL;

	uint32_t *data = mmap(NULL, bufsize,
			PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
	if (data == MAP_FAILED) {
		close(fd);
		return NULL;
	}

	struct wl_shm_pool *pool = wl_shm_create_pool(shm, fd, bufsize);
	struct wl_buffer *buffer = wl_shm_pool_create_buffer(pool, 0,
			width, height, stride, WL_SHM_FORMAT_ARGB8888);
	wl_buffer_add_listener(buffer, &wl_buffer_listener, NULL);
	wl_shm_pool_destroy(pool);
	close(fd);

	/* Colors (premultiplied!) */
	pixman_color_t textbgcolor = bgcolor;
	pixman_color_t textfgcolor = fgcolor;

	/* Pixman image corresponding to main buffer */
	pixman_image_t *bar = pixman_image_create_bits(PIXMAN_a8r8g8b8,
			width, height, data, width * 4);
	/* Fill bar with background color if bar should extend beyond text */
	if (!expand)
		pixman_image_fill_boxes(PIXMAN_OP_SRC, bar, &bgcolor, 1,
				&(pixman_box32_t) {.x1 = 0, .x2 = width, .y1 = 0, .y2 = height});

	/* Text background and foreground layers */
	pixman_image_t *background = pixman_image_create_bits(PIXMAN_a8r8g8b8,
			width, height, NULL, width * 4);
	pixman_image_t *foreground = pixman_image_create_bits(PIXMAN_a8r8g8b8,
			width, height, NULL, width * 4);

	pixman_image_t *fgfill = pixman_image_create_solid_fill(&textfgcolor);

	clickies = 0;

	/* Start drawing at center-left (ypos sets the text baseline) */
	uint32_t xpos = 0, maxxpos = 0;
	uint32_t ypos = (height + font->ascent - font->descent) / 2;

	uint32_t codepoint, lastcp = 0, state = UTF8_ACCEPT;

	clickstacktop = 0;
	for (char *p = text; *p; p++) {
		/* Check for inline ^ commands */
		if (state == UTF8_ACCEPT && *p == '^') {
			p++;
			if (*p != '^') {
				p = handle_cmd(p, &textbgcolor, &textfgcolor, &xpos, &ypos);
				pixman_image_unref(fgfill);
				fgfill = pixman_image_create_solid_fill(&textfgcolor);
				continue;
			}
		}

		/* Returns nonzero if more bytes are needed */
		if (utf8decode(&state, &codepoint, *p))
			continue;

		/* Turn off subpixel rendering, which complicates things when
		 * mixed with alpha channels */
		const struct fcft_glyph *glyph = fcft_rasterize_char_utf32(font, codepoint,
				FCFT_SUBPIXEL_NONE);
		if (!glyph)
			continue;

		/* Adjust x position based on kerning with previous glyph */
		long x_kern = 0;
		if (lastcp)
			fcft_kerning(font, lastcp, codepoint, &x_kern, NULL);
		xpos += x_kern;
		lastcp = codepoint;

		/* Detect and handle pre-rendered glyphs (e.g. emoji) */
		if (pixman_image_get_format(glyph->pix) == PIXMAN_a8r8g8b8) {
			/* Only the alpha channel of the mask is used, so we can
			 * use fgfill here to blend prerendered glyphs with the
			 * same opacity */
			pixman_image_composite32(
				PIXMAN_OP_OVER, glyph->pix, fgfill, foreground, 0, 0, 0, 0,
				xpos + glyph->x, ypos - glyph->y, glyph->width, glyph->height);
		} else {
			/* Applying the foreground color here would mess up
			 * component alphas for subpixel-rendered text, so we
			 * apply it when blending. */
			pixman_image_composite32(
				PIXMAN_OP_OVER, fgfill, glyph->pix, foreground, 0, 0, 0, 0,
				xpos + glyph->x, ypos - glyph->y, glyph->width, glyph->height);
		}

		if (xpos < width) {
			pixman_image_fill_boxes(PIXMAN_OP_OVER, background,
					&textbgcolor, 1, &(pixman_box32_t){
						.x1 = xpos,
						.x2 = MIN(xpos + glyph->advance.x, width),
						.y1 = 0,
						.y2 = height,
					});
		}

		/* increment pen position */
		xpos += glyph->advance.x;
		ypos += glyph->advance.y;
		maxxpos = MAX(maxxpos, xpos);
	}
	pixman_image_unref(fgfill);

	if (state != UTF8_ACCEPT)
		fprintf(stderr, "malformed UTF-8 sequence\n");

	/* Draw background and foreground on bar */
	int32_t xdraw;
	switch (titlealign) {
		case ALIGN_L:
			xdraw = 0;
			break;
		case ALIGN_R:
			xdraw = width - maxxpos;
			break;
		case ALIGN_C:
		default:
			xdraw = (width - maxxpos) / 2;
			break;
	}

	if (xdraw) {
		for (int i = 0; i < clickies; i++) {
			clickables[i].x1 += xdraw;
			clickables[i].x2 += xdraw;
		}
	}

	if (expand) {
		struct wl_region *inputregion = wl_compositor_create_region(compositor);
		wl_region_add(inputregion, xdraw, 0, MAX(maxxpos, 1), height);
		wl_surface_set_input_region(wl_surface, inputregion);
		wl_region_destroy(inputregion);
	}

	pixman_image_composite32(PIXMAN_OP_OVER, background, NULL, bar, 0, 0, 0, 0,
			xdraw, 0, width, height);
	pixman_image_composite32(PIXMAN_OP_OVER, foreground, NULL, bar, 0, 0, 0, 0,
			xdraw, 0, width, height);

	pixman_image_unref(foreground);
	pixman_image_unref(background);
	pixman_image_unref(bar);
	munmap(data, bufsize);
	return buffer;
}

/* Layer-surface setup adapted from layer-shell example in [wlroots] */
static void
layer_surface_configure(void *data,
		struct zwlr_layer_surface_v1 *surface,
		uint32_t serial, uint32_t w, uint32_t h)
{
	width = w;
	height = h;
	stride = width * 4;
	bufsize = stride * height;

	if (exclusive_zone > 0)
		exclusive_zone = height;
	zwlr_layer_surface_v1_set_exclusive_zone(layer_surface, exclusive_zone);
	zwlr_layer_surface_v1_ack_configure(surface, serial);

	struct wl_buffer *buffer = draw_frame(lastline);
	if (!buffer)
		return;
	wl_surface_attach(wl_surface, buffer, 0, 0);
	wl_surface_damage_buffer(wl_surface, 0, 0, width, height);
	wl_surface_commit(wl_surface);
}

static void
layer_surface_closed(void *data, struct zwlr_layer_surface_v1 *surface)
{
	zwlr_layer_surface_v1_destroy(surface);
	wl_surface_destroy(wl_surface);
	run_display = false;
}

static struct zwlr_layer_surface_v1_listener layer_surface_listener = {
	.configure = layer_surface_configure,
	.closed = layer_surface_closed,
};

struct input_state {
	struct wl_surface *surface;
	double x, y;
	uint32_t button;
};

static void
wl_pointer_enter(void *data, struct wl_pointer *wl_pointer,
			uint32_t serial, struct wl_surface *surface,
			wl_fixed_t surface_x, wl_fixed_t surface_y)
{
	struct input_state *istate = data;
	istate->surface = surface;
	istate->x = wl_fixed_to_double(surface_x);
	istate->y = wl_fixed_to_double(surface_y);
}

static void
wl_pointer_motion(void *data, struct wl_pointer *wl_pointer, uint32_t time,
		wl_fixed_t surface_x, wl_fixed_t surface_y)
{
	struct input_state *istate = data;
	istate->x = wl_fixed_to_double(surface_x);
	istate->y = wl_fixed_to_double(surface_y);
}

static void
wl_pointer_button(void *data, struct wl_pointer *wl_pointer, uint32_t serial,
		uint32_t time, uint32_t button, uint32_t state)
{
	struct input_state *istate = data;
	istate->button = state == WL_POINTER_BUTTON_STATE_RELEASED ? 0 : button;
}

static void
wl_pointer_leave(void *data, struct wl_pointer *wl_pointer,
		uint32_t serial, struct wl_surface *surface)
{
	struct input_state *istate = data;
	istate->surface = NULL;
}

static void
wl_pointer_axis(void *data, struct wl_pointer *wl_pointer, uint32_t time,
		uint32_t axis, wl_fixed_t value)
{
	struct input_state *istate = data;
	if (axis != cur_axis) {
		if (abs(value) < 4*cur_scroll)
			return;
		cur_axis = axis;
		cur_scrollcarry = 0;
	} else if ((value > 0) == (cur_scroll < 0))
		cur_scrollcarry = 0;
	cur_scroll = abs(value);
	cur_scrollcarry += cur_scroll;
	if (cur_scrollcarry > SCROLL_THRESHOLD) {
		cur_scrollcarry = MIN(SCROLL_THRESHOLD, cur_scrollcarry - SCROLL_THRESHOLD);
		istate->button = value > 0 ? 275 : 276;
	}
}

static void
wl_pointer_axis_source(void *data, struct wl_pointer *wl_pointer,
		uint32_t axis_source)
{
}

static void
wl_pointer_axis_stop(void *data, struct wl_pointer *wl_pointer,
		uint32_t time, uint32_t axis)
{
	struct input_state *istate = data;
	if (axis == cur_axis) {
		istate->button = 0;
		cur_axis = -1;
		cur_scroll = 0;
	}
}

static void
wl_pointer_axis_discrete(void *data, struct wl_pointer *wl_pointer,
			uint32_t axis, int32_t discrete)
{
}

void
spawn(const char *arg)
{
	static const char *shell = NULL;

	if (!arg)
		return;

	if (!shell && !(shell = getenv("SHELL")))
		shell = "/bin/sh";

	if (fork() == 0) {
		dup2(STDERR_FILENO, STDOUT_FILENO);
		setsid();
		execl(shell, shell, "-c", arg, (char *)NULL);
		EBARF("dtao: execl '%s -c %s' failed: ", shell, arg);
	}

	if (signal(SIGCHLD, SIG_IGN) == SIG_ERR)
		EBARF("failed to ignore SIGCHLD");
}

static void
wl_pointer_frame(void *data, struct wl_pointer *wl_pointer)
{
	struct input_state *istate = data;

	if (!istate || istate->button == 0)
		return;

	for (int i = 0; i < clickies; i++) {
		if (clickables[i].btn == istate->button - 271 &&
				istate->x >= clickables[i].x1 &&
				istate->x <= clickables[i].x2 &&
				istate->y >= clickables[i].y1 &&
				istate->y <= clickables[i].y2) {
//			do {
				spawn(clickables[i].cmd);
//			} while (istate->button >= 275 &&
//				 istate->button <= 276 &&
//				 --cur_scrollcarry > 0);
			break;
		}
	}

	istate->button = 0;
}

static const struct wl_pointer_listener wl_pointer_listener = {
	.enter = wl_pointer_enter,
	.leave = wl_pointer_leave,
	.motion = wl_pointer_motion,
	.button = wl_pointer_button,
	.axis = wl_pointer_axis,
	.axis_source = wl_pointer_axis_source,
	.axis_stop = wl_pointer_axis_stop,
	.axis_discrete = wl_pointer_axis_discrete,
	.frame = wl_pointer_frame,
};

static void
wl_seat_capabilities(void *data, struct wl_seat *wl_seat, uint32_t capabilities)
{
	struct input_state *istate = data;
	bool have_pointer = capabilities & WL_SEAT_CAPABILITY_POINTER;

	if (have_pointer && wl_pointer == NULL) {
		wl_pointer = wl_seat_get_pointer(wl_seat);
		wl_pointer_add_listener(wl_pointer,
				&wl_pointer_listener, istate);
	} else if (!have_pointer && wl_pointer != NULL) {
		wl_pointer_release(wl_pointer);
		wl_pointer = NULL;
	}
}

static void
wl_seat_name(void *data, struct wl_seat *wl_seat, const char *name)
{
	fprintf(stderr, "seat name: %s\n", name);
}

static const struct wl_seat_listener wl_seat_listener = {
	.capabilities = wl_seat_capabilities,
	.name = wl_seat_name,
};

static void
wl_output_geometry(void *data, struct wl_output *wl_output,
                int32_t x, int32_t y, int32_t w, int32_t h,
                int32_t subpixel, const char *make, const char *model,
                int32_t transform)
{
}

static void
wl_output_mode(void *data, struct wl_output *wl_output,
                uint32_t flags, int32_t width, int32_t height, int32_t refresh)
{
}

static void
wl_output_done(void *data, struct wl_output *wl_output)
{
}

static void
wl_output_scale(void *data, struct wl_output *wl_output,
                int32_t factor)
{
}

static void
wl_output_description(void *data, struct wl_output *output,
		const char *description)
{
}

static void
wl_output_name(void *data, struct wl_output *output, const char *name)
{
	if (!output_name) return;
	if (!strcmp(output_name, name))
		wl_output = output;
}

static const struct wl_output_listener output_listener = {
	.geometry = wl_output_geometry,
	.mode = wl_output_mode,
	.done = wl_output_done,
	.scale = wl_output_scale,
	.name = wl_output_name,
	.description = wl_output_description,
};

static void
handle_global(void *data, struct wl_registry *registry,
		uint32_t name, const char *interface, uint32_t version)
{
	struct input_state *istate = data;
	if (strcmp(interface, wl_compositor_interface.name) == 0) {
		compositor = wl_registry_bind(registry, name,
				&wl_compositor_interface, 4);
	} else if (strcmp(interface, wl_shm_interface.name) == 0) {
		shm = wl_registry_bind(registry, name, &wl_shm_interface, 1);
	} else if (strcmp(interface, wl_output_interface.name) == 0) {
		if (output_name) {
			if (version < 4)
				EBARF("wl_output_name not supported by compositor");
			wl_output_add_listener(wl_registry_bind(
					registry, name, &wl_output_interface, 4),
					&output_listener, NULL);
		} else {
			struct wl_output *o = wl_registry_bind(registry, name,
					&wl_output_interface, 1);
			if (output-- == 0)
				wl_output = o;
		}
	} else if (strcmp(interface, zwlr_layer_shell_v1_interface.name) == 0) {
		layer_shell = wl_registry_bind(registry, name,
				&zwlr_layer_shell_v1_interface, 1);
	} else if (strcmp(interface, wl_seat_interface.name) == 0) {
		wl_seat = wl_registry_bind(registry, name, &wl_seat_interface, 5);
		wl_seat_add_listener(wl_seat, &wl_seat_listener, istate);
	}
}

static void
handle_global_remove(void *data, struct wl_registry *wl_registry, uint32_t name)
{
}

static const struct wl_registry_listener registry_listener = {
	.global = handle_global,
	.global_remove = handle_global_remove,
};

static void
read_stdin(void)
{
	/* Read as much data as we can into line buffer */
	ssize_t b = read(STDIN_FILENO, line + linerem, MAX_LINE_LEN - linerem);
	if (b < 0)
		EBARF("read");
	if (b == 0) {
		eof_stdin = true;
		return;
	}
	linerem += b;

	/* Handle each line in the buffer in turn */
	char *curline, *end;
	struct wl_buffer *buffer = NULL;
	for (curline = line; (end = memchr(curline, '\n', linerem)); curline = end) {
		*end++ = '\0';
		linerem -= end - curline;

		if (eat_line) {
			eat_line = false;
			continue;
		}

		/* Keep last line for redrawing purposes */
		memcpy(lastline, curline, end - curline);

		if (!(buffer = draw_frame(lastline)))
			continue;
	}

	if (linerem == MAX_LINE_LEN || eat_line) {
		/* Buffer is full, so discard current line */
		linerem = 0;
		eat_line = true;
	} else if (linerem && curline != line) {
		/* Shift any remaining data over */
		memmove(line, curline, linerem);
	}

	/* Redraw if anything new was rendered */
	if (buffer) {
		wl_surface_attach(wl_surface, buffer, 0, 0);
		wl_surface_damage_buffer(wl_surface, 0, 0, width, height);
		wl_surface_commit(wl_surface);
	}
}

static void
event_loop(void)
{
	int ret;
	int wlfd = wl_display_get_fd(display);

	while (run_display && !(eof_stdin && persist == 0)) {
		fd_set rfds;
		FD_ZERO(&rfds);
		if (!eof_stdin)
			FD_SET(STDIN_FILENO, &rfds);

		FD_SET(wlfd, &rfds);

		/* Does this need to be inside the loop? */
		wl_display_flush(display);

		ret = select(wlfd + 1, &rfds, NULL, NULL, NULL);
		if (ret < 0)
			EBARF("select");

		if (!eof_stdin && FD_ISSET(STDIN_FILENO, &rfds))
			read_stdin();

		if (FD_ISSET(wlfd, &rfds))
			if (wl_display_dispatch(display) == -1)
				break;

		if (eof_stdin && persist > 0) {
			alarm(persist);
			persist = -1;
		}
	}
}

int
main(int argc, char **argv)
{
	char *namespace = "dtao";
	char *fontstr = "";
	char *actionstr = "";
	uint32_t layer = ZWLR_LAYER_SHELL_V1_LAYER_TOP;
	uint32_t anchor = ZWLR_LAYER_SURFACE_V1_ANCHOR_TOP |
			ZWLR_LAYER_SURFACE_V1_ANCHOR_LEFT |
			ZWLR_LAYER_SURFACE_V1_ANCHOR_RIGHT;
	int margintop = 0, marginbottom = 0, marginleft = 0, marginright = 0;

	/* Parse options */
	for (int i = 1; i < argc; i++) {
		if (!strcmp(argv[i], "-bg")) {
			if (++i >= argc)
				BARF("option -bg requires an argument");
			if (parse_color(argv[i], &bgcolor))
				BARF("malformed color string for -bg");
		} else if (!strcmp(argv[i], "-e")) {
			if (++i >= argc)
				BARF("option -e requires an argument");
			actionstr = argv[i];
		} else if (!strcmp(argv[i], "-expand")) {
			if (++i >= argc)
				BARF("option -expand requires an argument");
			expand = true;
			if (argv[i][0] == 'l')
				titlealign = ALIGN_R;
			else if (argv[i][0] == 'r')
				titlealign = ALIGN_L;
			else if (argv[i][0] == 'c')
				titlealign = ALIGN_C;
		} else if (!strcmp(argv[i], "-fg")) {
			if (++i >= argc)
				BARF("option -fg requires an argument");
			if (parse_color(argv[i], &fgcolor))
				BARF("malformed color string for -fg");
		} else if (!strcmp(argv[i], "-fn")) {
			if (++i >= argc)
				BARF("option -fn requires an argument");
			fontstr = argv[i];
		} else if (!strcmp(argv[i], "-h")) {
			if (++i >= argc)
				BARF("option -h requires an argument");
			height = atoi(argv[i]);
		} else if (!strcmp(argv[i], "-l")) {
			if (++i >= argc)
				BARF("option -l requires an argument");
			lines = atoi(argv[i]);
		} else if (!strcmp(argv[i], "-L")) {
			if (++i >= argc)
				BARF("option -L requires an argument");
			if (argv[i][0] == 'o')
				layer = ZWLR_LAYER_SHELL_V1_LAYER_OVERLAY;
			else if (argv[i][0] == 'b')
				layer = ZWLR_LAYER_SHELL_V1_LAYER_BOTTOM;
			else if (argv[i][0] == 'u')
				layer = ZWLR_LAYER_SHELL_V1_LAYER_BACKGROUND;
			else
				layer = ZWLR_LAYER_SHELL_V1_LAYER_TOP;
		} else if (!strcmp(argv[i], "-p")) {
			if (i + 1 >= argc || argv[i + 1][0] == '-' ||
					(persist = atoi(argv[++i])) == 0)
				persist = -1;
		} else if (!strcmp(argv[i], "-sa")) {
			if (++i >= argc)
				BARF("option -sa requires an argument");
			if (argv[i][0] == 'l')
				subalign = ALIGN_L;
			else if (argv[i][0] == 'r')
				subalign = ALIGN_R;
			else
				subalign = ALIGN_C;
		} else if (!strcmp(argv[i], "-ta")) {
			if (++i >= argc)
				BARF("option -ta requires an argument");
			/* Expand overrides alignment */
			if (!expand) {
				if (argv[i][0] == 'l')
					titlealign = ALIGN_L;
				else if (argv[i][0] == 'r')
					titlealign = ALIGN_R;
				else
					titlealign = ALIGN_C;
			}
		} else if (!strcmp(argv[i], "-tw")) {
			if (++i >= argc)
				BARF("option -tw requires an argument");
			titlewidth = atoi(argv[i]);
		} else if (!strcmp(argv[i], "-u")) {
			unified = 1;
		} else if (!strcmp(argv[i], "-v")) {
			fprintf(stderr, PROGRAM " " VERSION ", " COPYRIGHT "\n");
			return 0;
		} else if (!strcmp(argv[i], "-w")) {
			if (++i >= argc)
				BARF("option -w requires an argument");
			width = atoi(argv[i]);
		} else if (!strcmp(argv[i], "-xs")) {
			int j;
			if (++i >= argc)
				BARF("option -xs requires an argument");
			output = 0;
			for (j = 0; argv[i][j] && isdigit(argv[i][j]); j++)
				output = output * 10 + argv[i][j] - '0';
			if (argv[i][j])
				output_name = argv[i];
			else if (output > 0)
				output--; /* One-based to match dzen2 */
		} else if (!strcmp(argv[i], "-x")) {
			if (++i >= argc)
				BARF("option -x requires an argument");
			if (*argv[i] == '-')
				marginright = atoi(argv[i] + 1);
			else
				marginleft = atoi(argv[i]);
		} else if (!strcmp(argv[i], "-y")) {
			if (++i >= argc)
				BARF("option -y requires an argument");
			if (*argv[i] == '-') {
				marginbottom = atoi(argv[i] + 1);
				anchor |= ZWLR_LAYER_SURFACE_V1_ANCHOR_BOTTOM;
				anchor &= ~ZWLR_LAYER_SURFACE_V1_ANCHOR_TOP;
			} else {
				margintop = atoi(argv[i]);
				anchor |= ZWLR_LAYER_SURFACE_V1_ANCHOR_TOP;
				anchor &= ~ZWLR_LAYER_SURFACE_V1_ANCHOR_BOTTOM;
			}
		} else if (!strcmp(argv[i], "-z")) {
			exclusive_zone++;
		} else {
			BARF("option '%s' not recognized\n%s", argv[i], USAGE);
		}
	}

	/* Set up display and protocols */
	display = wl_display_connect(NULL);
	if (!display)
		BARF("Failed to create display");

	struct wl_registry *registry = wl_display_get_registry(display);
	struct input_state istate = {0};
	wl_registry_add_listener(registry, &registry_listener, &istate);
	wl_display_dispatch(display);
	wl_display_roundtrip(display);

	if (!compositor || !shm || !layer_shell)
		BARF("compositor does not support all needed protocols");

	/* Load selected font */
	fcft_init(FCFT_LOG_COLORIZE_AUTO, 0, FCFT_LOG_CLASS_ERROR);
	fcft_set_scaling_filter(FCFT_SCALING_FILTER_LANCZOS3);
	font = fcft_from_name(1, (const char *[]) {fontstr}, NULL);
	if (!font)
		BARF("could not load font");

	/* Create layer-shell surface */
	wl_surface = wl_compositor_create_surface(compositor);
	if (!wl_surface)
		BARF("could not create wl_surface");

	if (!wl_output && output >= 0) {
		if (output_name)
			BARF("could not bind to wl_output %s",
				output_name);
		else
			BARF("could not bind to wl_output");
	}

	layer_surface = zwlr_layer_shell_v1_get_layer_surface(layer_shell,
			wl_surface, wl_output, layer, namespace);
	if (!layer_surface)
		BARF("could not create layer_surface");
	zwlr_layer_surface_v1_add_listener(layer_surface,
			&layer_surface_listener, layer_surface);

	/* Set layer size and positioning */
	if (!height)
		height = font->ascent + font->descent;

	zwlr_layer_surface_v1_set_size(layer_surface, width, height);
	zwlr_layer_surface_v1_set_anchor(layer_surface, anchor);
	zwlr_layer_surface_v1_set_margin(layer_surface, margintop, marginright,
			marginbottom, marginleft);
	wl_surface_commit(wl_surface);
	wl_display_roundtrip(display);

	event_loop();

	/* Clean everything up */
	zwlr_layer_surface_v1_destroy(layer_surface);
	wl_surface_destroy(wl_surface);
	zwlr_layer_shell_v1_destroy(layer_shell);
	fcft_destroy(font);
	fcft_fini();
	wl_shm_destroy(shm);
	wl_compositor_destroy(compositor);
	wl_registry_destroy(registry);
	wl_display_disconnect(display);

	return 0;
}
