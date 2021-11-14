/*
 *  fplay.c - plays and records raw audio data
 *
 *  Copyright (c) by Jaroslav Kysela <perex@perex.cz>
 *  Based on vplay program by Michael Beck
 *
 *
 *   This program is free software; you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation; either version 2 of the License, or
 *   (at your option) any later version.
 *
 *   This program is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with this program; if not, write to the Free Software
 *   Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 * Modified 20211005 by AB1IP for SDR Utah (standalone portable version)
 */

#define _GNU_SOURCE
#include <stdio.h>
#include <malloc.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <fcntl.h>
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <time.h>
#include <locale.h>
#include <alsa/asoundlib.h>
#include <assert.h>
#include <termios.h>
#include <signal.h>
#include <poll.h>
#include <sys/uio.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <endian.h>

#define N_(x) (x)
#define _(x) (x)
#define gettext(x) (x)

#define SND_UTIL_VERSION_STR "fplay-1.0"

#define ABS(a)  (a) < 0 ? -(a) : (a)

#ifdef SND_CHMAP_API_VERSION
#define CONFIG_SUPPORT_CHMAP	1
#endif

#ifndef LLONG_MAX
#define LLONG_MAX    9223372036854775807LL
#endif

#ifndef le16toh
#include <asm/byteorder.h>
#define le16toh(x) __le16_to_cpu(x)
#define be16toh(x) __be16_to_cpu(x)
#define le32toh(x) __le32_to_cpu(x)
#define be32toh(x) __be32_to_cpu(x)
#endif

#define DEFAULT_FORMAT		SND_PCM_FORMAT_U8
#define DEFAULT_SPEED 		8000

/* global data */

static snd_pcm_sframes_t (*readi_func)(snd_pcm_t *handle, void *buffer, snd_pcm_uframes_t size);
static snd_pcm_sframes_t (*writei_func)(snd_pcm_t *handle, const void *buffer, snd_pcm_uframes_t size);
static snd_pcm_sframes_t (*readn_func)(snd_pcm_t *handle, void **bufs, snd_pcm_uframes_t size);
static snd_pcm_sframes_t (*writen_func)(snd_pcm_t *handle, void **bufs, snd_pcm_uframes_t size);

enum {
	VUMETER_NONE,
	VUMETER_MONO,
	VUMETER_STEREO
};

static char *command;
static snd_pcm_t *handle;
static struct {
	snd_pcm_format_t format;
	unsigned int channels;
	unsigned int rate;
} hwparams, rhwparams;
static int timelimit = 0;
static int sampleslimit = 0;
static int quiet_mode = 0;
static int open_mode = 0;
static snd_pcm_stream_t stream = SND_PCM_STREAM_PLAYBACK;
static int mmap_flag = 0;
static int interleaved = 1;
static int nonblock = 0;
static volatile sig_atomic_t in_aborting = 0;
static u_char *audiobuf = NULL;
static snd_pcm_uframes_t chunk_size = 0;
static unsigned period_time = 0;
static unsigned buffer_time = 0;
static snd_pcm_uframes_t period_frames = 0;
static snd_pcm_uframes_t buffer_frames = 0;
static int avail_min = -1;
static int start_delay = 0;
static int stop_delay = 0;
static int monotonic = 0;
static int interactive = 0;
static int can_pause = 0;
static int fatal_errors = 0;
static int verbose = 0;
static int vumeter = VUMETER_NONE;
static size_t significant_bits_per_sample, bits_per_sample, bits_per_frame;
static size_t chunk_bytes;
static int test_position = 0;
static int test_coef = 8;
static int test_nowait = 0;
static snd_output_t *log;
static long long max_file_size = 0;
static int max_file_time = 0;
static int use_strftime = 0;
volatile static int recycle_capture_file = 0;
static long term_c_lflag = -1;
static int dump_hw_params = 0;

static int fd = -1;
static off64_t pbrec_count = LLONG_MAX, fdcount;

static char *pidfile_name = NULL;
FILE *pidf = NULL;
static int pidfile_written = 0;

#ifdef CONFIG_SUPPORT_CHMAP
static snd_pcm_chmap_t *channel_map = NULL; /* chmap to override */
static unsigned int *hw_map = NULL; /* chmap to follow */
#endif

/* needed prototypes */

static void done_stdin(void);

static void playback(char *filename);
static void capture(char *filename);
static void playbackv(char **filenames, unsigned int count);
static void capturev(char **filenames, unsigned int count);

static void suspend(void);

#if __GNUC__ > 2 || (__GNUC__ == 2 && __GNUC_MINOR__ >= 95)
#define error(...) do {\
	fprintf(stderr, "%s: %s:%d: ", command, __func__, __LINE__); \
	fprintf(stderr, __VA_ARGS__); \
	putc('\n', stderr); \
} while (0)
#else
#define error(args...) do {\
	fprintf(stderr, "%s: %s:%d: ", command, __func__, __LINE__); \
	fprintf(stderr, ##args); \
	putc('\n', stderr); \
} while (0)
#endif	

static void usage(char *command)
{
	snd_pcm_format_t k;
	printf(
_("Usage: %s [OPTION]... [FILE]...\n"
"\n"
"-h, --help              help\n"
"    --version           print current version\n"
"-l, --list-devices      list all soundcards and digital audio devices\n"
"-L, --list-pcms         list device names\n"
"-D, --device=NAME       select PCM by name\n"
"-q, --quiet             quiet mode\n"
"-c, --channels=#        channels\n"
"-f, --format=FORMAT     sample format (case insensitive)\n"
"-r, --rate=#            sample rate\n"
"-d, --duration=#        interrupt after # seconds\n"
"-s, --samples=#         interrupt after # samples per channel\n"
"-M, --mmap              mmap stream\n"
"-N, --nonblock          nonblocking mode\n"
"-F, --period-time=#     distance between interrupts is # microseconds\n"
"-B, --buffer-time=#     buffer duration is # microseconds\n"
"    --period-size=#     distance between interrupts is # frames\n"
"    --buffer-size=#     buffer duration is # frames\n"
"-A, --avail-min=#       min available space for wakeup is # microseconds\n"
"-R, --start-delay=#     delay for automatic PCM start is # microseconds \n"
"                        (relative to buffer size if <= 0)\n"
"-T, --stop-delay=#      delay for automatic PCM stop is # microseconds from xrun\n"
"-v, --verbose           show PCM structure and setup (accumulative)\n"
"-V, --vumeter=TYPE      enable VU meter (TYPE: mono or stereo)\n"
"-I, --separate-channels one file for each channel\n"
"-i, --interactive       allow interactive operation from stdin\n"
"-m, --chmap=ch1,ch2,..  Give the channel map to override or follow\n"
"    --disable-resample  disable automatic rate resample\n"
"    --disable-channels  disable automatic channel conversions\n"
"    --disable-format    disable automatic format conversions\n"
"    --disable-softvol   disable software volume control (softvol)\n"
"    --test-position     test ring buffer position\n"
"    --test-coef=#       test coefficient for ring buffer position (default 8)\n"
"                        expression for validation is: coef * (buffer_size / 2)\n"
"    --test-nowait       do not wait for ring buffer - eats whole CPU\n"
"    --max-file-time=#   start another output file when the old file has recorded\n"
"                        for this many seconds\n"
"    --process-id-file   write the process ID here\n"
"    --use-strftime      apply the strftime facility to the output file name\n"
"    --dump-hw-params    dump hw_params of the device\n"
"    --fatal-errors      treat all errors as fatal\n"
  )
		, command);
	printf(_("Recognized sample formats are:"));
	for (k = 0; k <= SND_PCM_FORMAT_LAST; ++k) {
		const char *s = snd_pcm_format_name(k);
		if (s)
			printf(" %s", s);
	}
	printf(_("\nSome of these may not be available on selected hardware\n"));
	printf(_("The available format shortcuts are:\n"));
	printf(_("-f cd (16 bit little endian, 44100, stereo)\n"));
	printf(_("-f cdr (16 bit big endian, 44100, stereo)\n"));
	printf(_("-f dat (16 bit little endian, 48000, stereo)\n"));
}

static void device_list(void)
{
	snd_ctl_t *handle;
	int card, err, dev, idx;
	snd_ctl_card_info_t *info;
	snd_pcm_info_t *pcminfo;
	snd_ctl_card_info_alloca(&info);
	snd_pcm_info_alloca(&pcminfo);

	card = -1;
	if (snd_card_next(&card) < 0 || card < 0) {
		error(_("no soundcards found..."));
		return;
	}
	printf(_("**** List of %s Hardware Devices ****\n"),
	       snd_pcm_stream_name(stream));
	while (card >= 0) {
		char name[32];
		sprintf(name, "hw:%d", card);
		if ((err = snd_ctl_open(&handle, name, 0)) < 0) {
			error("control open (%i): %s", card, snd_strerror(err));
			goto next_card;
		}
		if ((err = snd_ctl_card_info(handle, info)) < 0) {
			error("control hardware info (%i): %s", card, snd_strerror(err));
			snd_ctl_close(handle);
			goto next_card;
		}
		dev = -1;
		while (1) {
			unsigned int count;
			if (snd_ctl_pcm_next_device(handle, &dev)<0)
				error("snd_ctl_pcm_next_device");
			if (dev < 0)
				break;
			snd_pcm_info_set_device(pcminfo, dev);
			snd_pcm_info_set_subdevice(pcminfo, 0);
			snd_pcm_info_set_stream(pcminfo, stream);
			if ((err = snd_ctl_pcm_info(handle, pcminfo)) < 0) {
				if (err != -ENOENT)
					error("control digital audio info (%i): %s", card, snd_strerror(err));
				continue;
			}
			printf(_("card %i: %s [%s], device %i: %s [%s]\n"),
				card, snd_ctl_card_info_get_id(info), snd_ctl_card_info_get_name(info),
				dev,
				snd_pcm_info_get_id(pcminfo),
				snd_pcm_info_get_name(pcminfo));
			count = snd_pcm_info_get_subdevices_count(pcminfo);
			printf( _("  Subdevices: %i/%i\n"),
				snd_pcm_info_get_subdevices_avail(pcminfo), count);
			for (idx = 0; idx < (int)count; idx++) {
				snd_pcm_info_set_subdevice(pcminfo, idx);
				if ((err = snd_ctl_pcm_info(handle, pcminfo)) < 0) {
					error("control digital audio playback info (%i): %s", card, snd_strerror(err));
				} else {
					printf(_("  Subdevice #%i: %s\n"),
						idx, snd_pcm_info_get_subdevice_name(pcminfo));
				}
			}
		}
		snd_ctl_close(handle);
	next_card:
		if (snd_card_next(&card) < 0) {
			error("snd_card_next");
			break;
		}
	}
}

static void pcm_list(void)
{
	void **hints, **n;
	char *name, *descr, *descr1, *io;
	const char *filter;

	if (snd_device_name_hint(-1, "pcm", &hints) < 0)
		return;
	n = hints;
	filter = stream == SND_PCM_STREAM_CAPTURE ? "Input" : "Output";
	while (*n != NULL) {
		name = snd_device_name_get_hint(*n, "NAME");
		descr = snd_device_name_get_hint(*n, "DESC");
		io = snd_device_name_get_hint(*n, "IOID");
		if (io != NULL && strcmp(io, filter) != 0)
			goto __end;
		printf("%s\n", name);
		if ((descr1 = descr) != NULL) {
			printf("    ");
			while (*descr1) {
				if (*descr1 == '\n')
					printf("\n    ");
				else
					putchar(*descr1);
				descr1++;
			}
			putchar('\n');
		}
	      __end:
	      	if (name != NULL)
	      		free(name);
		if (descr != NULL)
			free(descr);
		if (io != NULL)
			free(io);
		n++;
	}
	snd_device_name_free_hint(hints);
}

static void version(void)
{
	printf("%s: version " SND_UTIL_VERSION_STR " by Jaroslav Kysela <perex@perex.cz>\n", command);
}

/*
 *	Subroutine to clean up before exit.
 */
static void prg_exit(int code) 
{
	done_stdin();
	if (handle)
		snd_pcm_close(handle);
	if (pidfile_written)
		remove (pidfile_name);
	exit(code);
}

static void signal_handler(int sig)
{
	if (in_aborting)
		return;

	in_aborting = 1;
	if (verbose==2)
		putchar('\n');
	if (!quiet_mode)
		fprintf(stderr, _("Aborted by signal %s...\n"), strsignal(sig));
	if (handle)
		snd_pcm_abort(handle);
	if (sig == SIGABRT) {
		/* do not call snd_pcm_close() and abort immediately */
		handle = NULL;
		prg_exit(EXIT_FAILURE);
	}
	signal(sig, SIG_DFL);
}

/* call on SIGUSR1 signal. */
static void signal_handler_recycle (int sig)
{
	/* flag the capture loop to start a new output file */
	recycle_capture_file = 1;
}

enum {
	OPT_VERSION = 1,
	OPT_PERIOD_SIZE,
	OPT_BUFFER_SIZE,
	OPT_DISABLE_RESAMPLE,
	OPT_DISABLE_CHANNELS,
	OPT_DISABLE_FORMAT,
	OPT_DISABLE_SOFTVOL,
	OPT_TEST_POSITION,
	OPT_TEST_COEF,
	OPT_TEST_NOWAIT,
	OPT_MAX_FILE_TIME,
	OPT_PROCESS_ID_FILE,
	OPT_USE_STRFTIME,
	OPT_DUMP_HWPARAMS,
	OPT_FATAL_ERRORS,
};

/*
 * make sure we write all bytes or return an error
 */
static ssize_t xwrite(int fd, const void *buf, size_t count)
{
	ssize_t written;
	size_t offset = 0;

	while (offset < count) {
		written = write(fd, (char *)buf + offset, count - offset);
		if (written <= 0)
			return written;

		offset += written;
	};

	return offset;
}

static long parse_long(const char *str, int *err)
{
	long val;
	char *endptr;

	errno = 0;
	val = strtol(str, &endptr, 0);

	if (errno != 0 || *endptr != '\0')
		*err = -1;
	else
		*err = 0;

	return val;
}

int main(int argc, char *argv[])
{
	int duration_or_sample = 0;
	int option_index;
	static const char short_options[] = "hnlLD:qc:f:r:d:s:MNF:A:R:T:B:vV:IPCi"
#ifdef CONFIG_SUPPORT_CHMAP
		"m:"
#endif
		;
	static const struct option long_options[] = {
		{"help", 0, 0, 'h'},
		{"version", 0, 0, OPT_VERSION},
		{"list-devnames", 0, 0, 'n'},
		{"list-devices", 0, 0, 'l'},
		{"list-pcms", 0, 0, 'L'},
		{"device", 1, 0, 'D'},
		{"quiet", 0, 0, 'q'},
		{"channels", 1, 0, 'c'},
		{"format", 1, 0, 'f'},
		{"rate", 1, 0, 'r'},
		{"duration", 1, 0 ,'d'},
		{"samples", 1, 0, 's'},
		{"mmap", 0, 0, 'M'},
		{"nonblock", 0, 0, 'N'},
		{"period-time", 1, 0, 'F'},
		{"period-size", 1, 0, OPT_PERIOD_SIZE},
		{"avail-min", 1, 0, 'A'},
		{"start-delay", 1, 0, 'R'},
		{"stop-delay", 1, 0, 'T'},
		{"buffer-time", 1, 0, 'B'},
		{"buffer-size", 1, 0, OPT_BUFFER_SIZE},
		{"verbose", 0, 0, 'v'},
		{"vumeter", 1, 0, 'V'},
		{"separate-channels", 0, 0, 'I'},
		{"playback", 0, 0, 'P'},
		{"capture", 0, 0, 'C'},
		{"disable-resample", 0, 0, OPT_DISABLE_RESAMPLE},
		{"disable-channels", 0, 0, OPT_DISABLE_CHANNELS},
		{"disable-format", 0, 0, OPT_DISABLE_FORMAT},
		{"disable-softvol", 0, 0, OPT_DISABLE_SOFTVOL},
		{"test-position", 0, 0, OPT_TEST_POSITION},
		{"test-coef", 1, 0, OPT_TEST_COEF},
		{"test-nowait", 0, 0, OPT_TEST_NOWAIT},
		{"max-file-time", 1, 0, OPT_MAX_FILE_TIME},
		{"process-id-file", 1, 0, OPT_PROCESS_ID_FILE},
		{"use-strftime", 0, 0, OPT_USE_STRFTIME},
		{"interactive", 0, 0, 'i'},
		{"dump-hw-params", 0, 0, OPT_DUMP_HWPARAMS},
		{"fatal-errors", 0, 0, OPT_FATAL_ERRORS},
#ifdef CONFIG_SUPPORT_CHMAP
		{"chmap", 1, 0, 'm'},
#endif
		{0, 0, 0, 0}
	};
	char *pcm_name = "default";
	int tmp, err, c;
	int do_device_list = 0, do_pcm_list = 0, force_sample_format = 0;
	snd_pcm_info_t *info;
	FILE *direction;

#ifdef ENABLE_NLS
	setlocale(LC_ALL, "");
	textdomain(PACKAGE);
#endif

	snd_pcm_info_alloca(&info);

	err = snd_output_stdio_attach(&log, stderr, 0);
	assert(err >= 0);

	command = argv[0];
	stream = SND_PCM_STREAM_PLAYBACK;
	direction = stdin;

	if (isatty(fileno(direction)) && (argc == 1)) {
		usage(command);
		return 1;
	}

	chunk_size = -1;
	rhwparams.format = DEFAULT_FORMAT;
	rhwparams.rate = DEFAULT_SPEED;
	rhwparams.channels = 1;

	while ((c = getopt_long(argc, argv, short_options, long_options, &option_index)) != -1) {
		switch (c) {
		case 'h':
			usage(command);
			return 0;
		case OPT_VERSION:
			version();
			return 0;
		case 'l':
			do_device_list = 1;
			break;
		case 'L':
			do_pcm_list = 1;
			break;
		case 'D':
			pcm_name = optarg;
			break;
		case 'q':
			quiet_mode = 1;
			break;
		case 'c':
			rhwparams.channels = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid channels argument '%s'"), optarg);
				return 1;
			}
			if (rhwparams.channels < 1 || rhwparams.channels > 256) {
				error(_("value %i for channels is invalid"), rhwparams.channels);
				return 1;
			}
			break;
		case 'f':
			force_sample_format = 1;
			if (strcasecmp(optarg, "cd") == 0 || strcasecmp(optarg, "cdr") == 0) {
				if (strcasecmp(optarg, "cdr") == 0)
					rhwparams.format = SND_PCM_FORMAT_S16_BE;
				else
					rhwparams.format = SND_PCM_FORMAT_S16_LE;
				rhwparams.rate = 44100;
				rhwparams.channels = 2;
			} else if (strcasecmp(optarg, "dat") == 0) {
				rhwparams.format = SND_PCM_FORMAT_S16_LE;
				rhwparams.rate = 48000;
				rhwparams.channels = 2;
			} else {
				rhwparams.format = snd_pcm_format_value(optarg);
				if (rhwparams.format == SND_PCM_FORMAT_UNKNOWN) {
					error(_("wrong extended format '%s'"), optarg);
					prg_exit(EXIT_FAILURE);
				}
			}
			break;
		case 'r':
			tmp = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid rate argument '%s'"), optarg);
				return 1;
			}
			if (tmp < 1000)
				tmp *= 1000;
			rhwparams.rate = tmp;
			break;
		case 'd':
			if (duration_or_sample) {
				error(_("duration and samples arguments cannot be used together"));
				return 1;
			}
			timelimit = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid duration argument '%s'"), optarg);
				return 1;
			}
			duration_or_sample = 1;
			break;
		case 's':
			if (duration_or_sample) {
				error(_("samples and duration arguments cannot be used together"));
				return 1;
			}
			sampleslimit = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid samples argument '%s'"), optarg);
				return 1;
			}
			duration_or_sample = 1;
			break;
		case 'N':
			nonblock = 1;
			open_mode |= SND_PCM_NONBLOCK;
			break;
		case 'F':
			period_time = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid period time argument '%s'"), optarg);
				return 1;
			}
			break;
		case 'B':
			buffer_time = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid buffer time argument '%s'"), optarg);
				return 1;
			}
			break;
		case OPT_PERIOD_SIZE:
			period_frames = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid period size argument '%s'"), optarg);
				return 1;
			}
			break;
		case OPT_BUFFER_SIZE:
			buffer_frames = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid buffer size argument '%s'"), optarg);
				return 1;
			}
			break;
		case 'A':
			avail_min = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid min available space argument '%s'"), optarg);
				return 1;
			}
			break;
		case 'R':
			start_delay = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid start delay argument '%s'"), optarg);
				return 1;
			}
			break;
		case 'T':
			stop_delay = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid stop delay argument '%s'"), optarg);
				return 1;
			}
			break;
		case 'v':
			verbose++;
			if (verbose > 1 && !vumeter)
				vumeter = VUMETER_MONO;
			break;
		case 'V':
			if (*optarg == 's')
				vumeter = VUMETER_STEREO;
			else if (*optarg == 'm')
				vumeter = VUMETER_MONO;
			else
				vumeter = VUMETER_NONE;
			break;
		case 'M':
			mmap_flag = 1;
			break;
		case 'I':
			interleaved = 0;
			break;
		case 'P':
			stream = SND_PCM_STREAM_PLAYBACK;
			command = "aplay";
			break;
		case 'C':
			stream = SND_PCM_STREAM_CAPTURE;
			command = "arecord";
			start_delay = 1;
			break;
		case 'i':
			interactive = 1;
			break;
		case OPT_DISABLE_RESAMPLE:
			open_mode |= SND_PCM_NO_AUTO_RESAMPLE;
			break;
		case OPT_DISABLE_CHANNELS:
			open_mode |= SND_PCM_NO_AUTO_CHANNELS;
			break;
		case OPT_DISABLE_FORMAT:
			open_mode |= SND_PCM_NO_AUTO_FORMAT;
			break;
		case OPT_DISABLE_SOFTVOL:
			open_mode |= SND_PCM_NO_SOFTVOL;
			break;
		case OPT_TEST_POSITION:
			test_position = 1;
			break;
		case OPT_TEST_COEF:
			test_coef = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid test coef argument '%s'"), optarg);
				return 1;
			}
			if (test_coef < 1)
				test_coef = 1;
			break;
		case OPT_TEST_NOWAIT:
			test_nowait = 1;
			break;
		case OPT_MAX_FILE_TIME:
			max_file_time = parse_long(optarg, &err);
			if (err < 0) {
				error(_("invalid max file time argument '%s'"), optarg);
				return 1;
			}
			break;
		case OPT_PROCESS_ID_FILE:
			pidfile_name = optarg;
			break;
		case OPT_USE_STRFTIME:
			use_strftime = 1;
			break;
		case OPT_DUMP_HWPARAMS:
			dump_hw_params = 1;
			break;
		case OPT_FATAL_ERRORS:
			fatal_errors = 1;
			break;
#ifdef CONFIG_SUPPORT_CHMAP
		case 'm':
			channel_map = snd_pcm_chmap_parse_string(optarg);
			if (!channel_map) {
				fprintf(stderr, _("Unable to parse channel map string: %s\n"), optarg);
				return 1;
			}
			break;
#endif
		default:
			fprintf(stderr, _("Try `%s --help' for more information.\n"), command);
			return 1;
		}
	}

	if (do_device_list) {
		if (do_pcm_list) pcm_list();
		device_list();
		goto __end;
	} else if (do_pcm_list) {
		pcm_list();
		goto __end;
	}

	err = snd_pcm_open(&handle, pcm_name, stream, open_mode);
	if (err < 0) {
		error(_("audio open error: %s"), snd_strerror(err));
		return 1;
	}

	if ((err = snd_pcm_info(handle, info)) < 0) {
		error(_("info error: %s"), snd_strerror(err));
		return 1;
	}

	if (nonblock) {
		err = snd_pcm_nonblock(handle, 1);
		if (err < 0) {
			error(_("nonblock setting error: %s"), snd_strerror(err));
			return 1;
		}
	}

	if (!force_sample_format &&
	    isatty(fileno(stdin)) &&
	    stream == SND_PCM_STREAM_CAPTURE &&
	    snd_pcm_format_width(rhwparams.format) <= 8)
		fprintf(stderr, "Warning: Some sources (like microphones) may produce inaudiable results\n"
				"         with 8-bit sampling. Use '-f' argument to increase resolution\n"
				"         e.g. '-f S16_LE'.\n");

	chunk_size = 1024;
	hwparams = rhwparams;

	audiobuf = (u_char *)malloc(1024);
	if (audiobuf == NULL) {
		error(_("not enough memory"));
		return 1;
	}

	if (mmap_flag) {
		writei_func = snd_pcm_mmap_writei;
		readi_func = snd_pcm_mmap_readi;
		writen_func = snd_pcm_mmap_writen;
		readn_func = snd_pcm_mmap_readn;
	} else {
		writei_func = snd_pcm_writei;
		readi_func = snd_pcm_readi;
		writen_func = snd_pcm_writen;
		readn_func = snd_pcm_readn;
	}

	if (pidfile_name) {
		errno = 0;
		pidf = fopen (pidfile_name, "w");
		if (pidf) {
			(void)fprintf (pidf, "%d\n", getpid());
			fclose(pidf);
			pidfile_written = 1;
		} else {
			error(_("Cannot create process ID file %s: %s"), 
				pidfile_name, strerror (errno));
			return 1;
		}
	}

	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);
	signal(SIGABRT, signal_handler);
	signal(SIGUSR1, signal_handler_recycle);
	if (interleaved) {
		if (optind > argc - 1) {
			if (stream == SND_PCM_STREAM_PLAYBACK)
				playback(NULL);
			else
				capture(NULL);
		} else {
			while (optind <= argc - 1) {
				if (stream == SND_PCM_STREAM_PLAYBACK)
					playback(argv[optind++]);
				else
					capture(argv[optind++]);
			}
		}
	} else {
		if (stream == SND_PCM_STREAM_PLAYBACK)
			playbackv(&argv[optind], argc - optind);
		else
			capturev(&argv[optind], argc - optind);
	}
	if (verbose==2)
		putchar('\n');
	snd_pcm_close(handle);
	handle = NULL;
	free(audiobuf);
      __end:
	snd_output_close(log);
	snd_config_update_free_global();
	prg_exit(EXIT_SUCCESS);
	/* avoid warning */
	return EXIT_SUCCESS;
}

/*
 * Safe read (for pipes)
 */
 
static ssize_t safe_read(int fd, void *buf, size_t count)
{
	ssize_t result = 0, res;

	while (count > 0 && !in_aborting) {
		if ((res = read(fd, buf, count)) == 0)
			break;
		if (res < 0)
			return result > 0 ? result : res;
		count -= res;
		result += res;
		buf = (char *)buf + res;
	}
	return result;
}

static void show_available_sample_formats(snd_pcm_hw_params_t* params)
{
	snd_pcm_format_t format;

	fprintf(stderr, "Available formats:\n");
	for (format = 0; format <= SND_PCM_FORMAT_LAST; format++) {
		if (snd_pcm_hw_params_test_format(handle, params, format) == 0)
			fprintf(stderr, "- %s\n", snd_pcm_format_name(format));
	}
}

#ifdef CONFIG_SUPPORT_CHMAP
static int setup_chmap(void)
{
	snd_pcm_chmap_t *chmap = channel_map;
	char mapped[hwparams.channels];
	snd_pcm_chmap_t *hw_chmap;
	unsigned int ch, i;
	int err;

	if (!chmap)
		return 0;

	if (chmap->channels != hwparams.channels) {
		error(_("Channel numbers don't match between hw_params and channel map"));
		return -1;
	}
	err = snd_pcm_set_chmap(handle, chmap);
	if (!err)
		return 0;

	hw_chmap = snd_pcm_get_chmap(handle);
	if (!hw_chmap) {
		fprintf(stderr, _("Warning: unable to get channel map\n"));
		return 0;
	}

	if (hw_chmap->channels == chmap->channels &&
	    !memcmp(hw_chmap, chmap, 4 * (chmap->channels + 1))) {
		/* maps are identical, so no need to convert */
		free(hw_chmap);
		return 0;
	}

	hw_map = calloc(hwparams.channels, sizeof(int));
	if (!hw_map) {
		error(_("not enough memory"));
		free(hw_chmap);
		return -1;
	}

	memset(mapped, 0, sizeof(mapped));
	for (ch = 0; ch < hw_chmap->channels; ch++) {
		if (chmap->pos[ch] == hw_chmap->pos[ch]) {
			mapped[ch] = 1;
			hw_map[ch] = ch;
			continue;
		}
		for (i = 0; i < hw_chmap->channels; i++) {
			if (!mapped[i] && chmap->pos[ch] == hw_chmap->pos[i]) {
				mapped[i] = 1;
				hw_map[ch] = i;
				break;
			}
		}
		if (i >= hw_chmap->channels) {
			char buf[256];
			error(_("Channel %d doesn't match with hw_params"), ch);
			snd_pcm_chmap_print(hw_chmap, sizeof(buf), buf);
			fprintf(stderr, "hardware chmap = %s\n", buf);
			free(hw_chmap);
			return -1;
		}
	}
	free(hw_chmap);
	return 0;
}
#else
#define setup_chmap()	0
#endif

static void set_params(void)
{
	snd_pcm_hw_params_t *params;
	snd_pcm_sw_params_t *swparams;
	snd_pcm_uframes_t buffer_size;
	int err;
	size_t n;
	unsigned int rate;
	snd_pcm_uframes_t start_threshold, stop_threshold;
	snd_pcm_hw_params_alloca(&params);
	snd_pcm_sw_params_alloca(&swparams);
	err = snd_pcm_hw_params_any(handle, params);
	if (err < 0) {
		error(_("Broken configuration for this PCM: no configurations available"));
		prg_exit(EXIT_FAILURE);
	}
	if (dump_hw_params) {
		fprintf(stderr, _("HW Params of device \"%s\":\n"),
			snd_pcm_name(handle));
		fprintf(stderr, "--------------------\n");
		snd_pcm_hw_params_dump(params, log);
		fprintf(stderr, "--------------------\n");
	}
	if (mmap_flag) {
		snd_pcm_access_mask_t *mask = alloca(snd_pcm_access_mask_sizeof());
		snd_pcm_access_mask_none(mask);
		snd_pcm_access_mask_set(mask, SND_PCM_ACCESS_MMAP_INTERLEAVED);
		snd_pcm_access_mask_set(mask, SND_PCM_ACCESS_MMAP_NONINTERLEAVED);
		snd_pcm_access_mask_set(mask, SND_PCM_ACCESS_MMAP_COMPLEX);
		err = snd_pcm_hw_params_set_access_mask(handle, params, mask);
	} else if (interleaved)
		err = snd_pcm_hw_params_set_access(handle, params,
						   SND_PCM_ACCESS_RW_INTERLEAVED);
	else
		err = snd_pcm_hw_params_set_access(handle, params,
						   SND_PCM_ACCESS_RW_NONINTERLEAVED);
	if (err < 0) {
		error(_("Access type not available"));
		prg_exit(EXIT_FAILURE);
	}
	err = snd_pcm_hw_params_set_format(handle, params, hwparams.format);
	if (err < 0) {
		error(_("Sample format non available"));
		show_available_sample_formats(params);
		prg_exit(EXIT_FAILURE);
	}
	err = snd_pcm_hw_params_set_channels(handle, params, hwparams.channels);
	if (err < 0) {
		error(_("Channels count non available"));
		prg_exit(EXIT_FAILURE);
	}

#if 0
	err = snd_pcm_hw_params_set_periods_min(handle, params, 2);
	assert(err >= 0);
#endif
	rate = hwparams.rate;
	err = snd_pcm_hw_params_set_rate_near(handle, params, &hwparams.rate, 0);
	assert(err >= 0);
	if ((float)rate * 1.05 < hwparams.rate || (float)rate * 0.95 > hwparams.rate) {
		if (!quiet_mode) {
			char plugex[64];
			const char *pcmname = snd_pcm_name(handle);
			fprintf(stderr, _("Warning: rate is not accurate (requested = %iHz, got = %iHz)\n"), rate, hwparams.rate);
			if (! pcmname || strchr(snd_pcm_name(handle), ':'))
				*plugex = 0;
			else
				snprintf(plugex, sizeof(plugex), "(-Dplug:%s)",
					 snd_pcm_name(handle));
			fprintf(stderr, _("         please, try the plug plugin %s\n"),
				plugex);
		}
	}
	rate = hwparams.rate;
	if (buffer_time == 0 && buffer_frames == 0) {
		err = snd_pcm_hw_params_get_buffer_time_max(params,
							    &buffer_time, 0);
		assert(err >= 0);
		if (buffer_time > 500000)
			buffer_time = 500000;
	}
	if (period_time == 0 && period_frames == 0) {
		if (buffer_time > 0)
			period_time = buffer_time / 4;
		else
			period_frames = buffer_frames / 4;
	}
	if (period_time > 0)
		err = snd_pcm_hw_params_set_period_time_near(handle, params,
							     &period_time, 0);
	else
		err = snd_pcm_hw_params_set_period_size_near(handle, params,
							     &period_frames, 0);
	assert(err >= 0);
	if (buffer_time > 0) {
		err = snd_pcm_hw_params_set_buffer_time_near(handle, params,
							     &buffer_time, 0);
	} else {
		err = snd_pcm_hw_params_set_buffer_size_near(handle, params,
							     &buffer_frames);
	}
	assert(err >= 0);
	monotonic = snd_pcm_hw_params_is_monotonic(params);
	can_pause = snd_pcm_hw_params_can_pause(params);
	err = snd_pcm_hw_params(handle, params);
	if (err < 0) {
		error(_("Unable to install hw params:"));
		snd_pcm_hw_params_dump(params, log);
		prg_exit(EXIT_FAILURE);
	}
	snd_pcm_hw_params_get_period_size(params, &chunk_size, 0);
	snd_pcm_hw_params_get_buffer_size(params, &buffer_size);
	if (chunk_size == buffer_size) {
		error(_("Can't use period equal to buffer size (%lu == %lu)"),
		      chunk_size, buffer_size);
		prg_exit(EXIT_FAILURE);
	}
	err = snd_pcm_sw_params_current(handle, swparams);
	if (err < 0) {
		error(_("Unable to get current sw params."));
		prg_exit(EXIT_FAILURE);
	}
	if (avail_min < 0)
		n = chunk_size;
	else
		n = (double) rate * avail_min / 1000000;
	err = snd_pcm_sw_params_set_avail_min(handle, swparams, n);

	/* round up to closest transfer boundary */
	n = buffer_size;
	if (start_delay <= 0) {
		start_threshold = n + (double) rate * start_delay / 1000000;
	} else
		start_threshold = (double) rate * start_delay / 1000000;
	if (start_threshold < 1)
		start_threshold = 1;
	if (start_threshold > n)
		start_threshold = n;
	err = snd_pcm_sw_params_set_start_threshold(handle, swparams, start_threshold);
	assert(err >= 0);
	if (stop_delay <= 0) 
		stop_threshold = buffer_size + (double) rate * stop_delay / 1000000;
	else
		stop_threshold = (double) rate * stop_delay / 1000000;
	err = snd_pcm_sw_params_set_stop_threshold(handle, swparams, stop_threshold);
	assert(err >= 0);

	if (snd_pcm_sw_params(handle, swparams) < 0) {
		error(_("unable to install sw params:"));
		snd_pcm_sw_params_dump(swparams, log);
		prg_exit(EXIT_FAILURE);
	}

	if (setup_chmap())
		prg_exit(EXIT_FAILURE);

	if (verbose)
		snd_pcm_dump(handle, log);

	bits_per_sample = snd_pcm_format_physical_width(hwparams.format);
	significant_bits_per_sample = snd_pcm_format_width(hwparams.format);
	bits_per_frame = bits_per_sample * hwparams.channels;
	chunk_bytes = chunk_size * bits_per_frame / 8;
	audiobuf = realloc(audiobuf, chunk_bytes);
	if (audiobuf == NULL) {
		error(_("not enough memory"));
		prg_exit(EXIT_FAILURE);
	}
	// fprintf(stderr, "real chunk_size = %i, frags = %i, total = %i\n", chunk_size, setup.buf.block.frags, setup.buf.block.frags * chunk_size);

	/* stereo VU-meter isn't always available... */
	if (vumeter == VUMETER_STEREO) {
		if (hwparams.channels != 2 || !interleaved || verbose > 2)
			vumeter = VUMETER_MONO;
	}

	/* show mmap buffer arragment */
	if (mmap_flag && verbose) {
		const snd_pcm_channel_area_t *areas;
		snd_pcm_uframes_t offset, size = chunk_size;
		int i;
		err = snd_pcm_mmap_begin(handle, &areas, &offset, &size);
		if (err < 0) {
			error(_("snd_pcm_mmap_begin problem: %s"), snd_strerror(err));
			prg_exit(EXIT_FAILURE);
		}
		for (i = 0; i < hwparams.channels; i++)
			fprintf(stderr, "mmap_area[%i] = %p,%u,%u (%u)\n", i, areas[i].addr, areas[i].first, areas[i].step, snd_pcm_format_physical_width(hwparams.format));
		/* not required, but for sure */
		snd_pcm_mmap_commit(handle, offset, 0);
	}

	buffer_frames = buffer_size;	/* for position test */
}

static void init_stdin(void)
{
	struct termios term;
	long flags;

	if (!interactive)
		return;
	if (!isatty(fileno(stdin))) {
		interactive = 0;
		return;
	}
	tcgetattr(fileno(stdin), &term);
	term_c_lflag = term.c_lflag;
	if (fd == fileno(stdin))
		return;
	flags = fcntl(fileno(stdin), F_GETFL);
	if (flags < 0 || fcntl(fileno(stdin), F_SETFL, flags|O_NONBLOCK) < 0)
		fprintf(stderr, _("stdin O_NONBLOCK flag setup failed\n"));
	term.c_lflag &= ~ICANON;
	tcsetattr(fileno(stdin), TCSANOW, &term);
}

static void done_stdin(void)
{
	struct termios term;

	if (!interactive)
		return;
	if (fd == fileno(stdin) || term_c_lflag == -1)
		return;
	tcgetattr(fileno(stdin), &term);
	term.c_lflag = term_c_lflag;
	tcsetattr(fileno(stdin), TCSANOW, &term);
}

static char wait_for_input(void)
{
	struct pollfd pfd;
	unsigned char b;

	do {
		pfd.fd = fileno(stdin);
		pfd.events = POLLIN;
		poll(&pfd, 1, -1);
	} while (read(fileno(stdin), &b, 1) != 1);
	return b;
}

static void do_pause(void)
{
	int err;
	unsigned char b;

	if (!can_pause) {
		fprintf(stderr, _("\rPAUSE command ignored (no hw support)\n"));
		return;
	}
	if (snd_pcm_state(handle) == SND_PCM_STATE_SUSPENDED)
		suspend();

	err = snd_pcm_pause(handle, 1);
	if (err < 0) {
		error(_("pause push error: %s"), snd_strerror(err));
		return;
	}
	while (1) {
		b = wait_for_input();
		if (b == ' ' || b == '\r') {
			while (read(fileno(stdin), &b, 1) == 1);
			if (snd_pcm_state(handle) == SND_PCM_STATE_SUSPENDED)
				suspend();
			err = snd_pcm_pause(handle, 0);
			if (err < 0)
				error(_("pause release error: %s"), snd_strerror(err));
			return;
		}
	}
}

static void check_stdin(void)
{
	unsigned char b;

	if (!interactive)
		return;
	if (fd != fileno(stdin)) {
		while (read(fileno(stdin), &b, 1) == 1) {
			if (b == ' ' || b == '\r') {
				while (read(fileno(stdin), &b, 1) == 1);
				fprintf(stderr, _("\r=== PAUSE ===                                                            "));
				fflush(stderr);
				do_pause();
				fprintf(stderr, "                                                                          \r");
				fflush(stderr);
			}
		}
	}
}

#ifndef timersub
#define	timersub(a, b, result) \
do { \
	(result)->tv_sec = (a)->tv_sec - (b)->tv_sec; \
	(result)->tv_usec = (a)->tv_usec - (b)->tv_usec; \
	if ((result)->tv_usec < 0) { \
		--(result)->tv_sec; \
		(result)->tv_usec += 1000000; \
	} \
} while (0)
#endif

#ifndef timermsub
#define	timermsub(a, b, result) \
do { \
	(result)->tv_sec = (a)->tv_sec - (b)->tv_sec; \
	(result)->tv_nsec = (a)->tv_nsec - (b)->tv_nsec; \
	if ((result)->tv_nsec < 0) { \
		--(result)->tv_sec; \
		(result)->tv_nsec += 1000000000L; \
	} \
} while (0)
#endif

/* I/O error handler */
static void xrun(void)
{
	snd_pcm_status_t *status;
	int res;
	
	snd_pcm_status_alloca(&status);
	if ((res = snd_pcm_status(handle, status))<0) {
		error(_("status error: %s"), snd_strerror(res));
		prg_exit(EXIT_FAILURE);
	}
	if (snd_pcm_status_get_state(status) == SND_PCM_STATE_XRUN) {
		if (fatal_errors) {
			error(_("fatal %s: %s"),
					stream == SND_PCM_STREAM_PLAYBACK ? _("underrun") : _("overrun"),
					snd_strerror(res));
			prg_exit(EXIT_FAILURE);
		}
		if (monotonic) {
#ifdef HAVE_CLOCK_GETTIME
			struct timespec now, diff, tstamp;
			clock_gettime(CLOCK_MONOTONIC, &now);
			snd_pcm_status_get_trigger_htstamp(status, &tstamp);
			timermsub(&now, &tstamp, &diff);
			fprintf(stderr, _("%s!!! (at least %.3f ms long)\n"),
				stream == SND_PCM_STREAM_PLAYBACK ? _("underrun") : _("overrun"),
				diff.tv_sec * 1000 + diff.tv_nsec / 1000000.0);
#else
			fprintf(stderr, "%s !!!\n", _("underrun"));
#endif
		} else {
			struct timeval now, diff, tstamp;
			gettimeofday(&now, 0);
			snd_pcm_status_get_trigger_tstamp(status, &tstamp);
			timersub(&now, &tstamp, &diff);
			fprintf(stderr, _("%s!!! (at least %.3f ms long)\n"),
				stream == SND_PCM_STREAM_PLAYBACK ? _("underrun") : _("overrun"),
				diff.tv_sec * 1000 + diff.tv_usec / 1000.0);
		}
		if (verbose) {
			fprintf(stderr, _("Status:\n"));
			snd_pcm_status_dump(status, log);
		}
		if ((res = snd_pcm_prepare(handle))<0) {
			error(_("xrun: prepare error: %s"), snd_strerror(res));
			prg_exit(EXIT_FAILURE);
		}
		return;		/* ok, data should be accepted again */
	}
	if (snd_pcm_status_get_state(status) == SND_PCM_STATE_DRAINING) {
		if (verbose) {
			fprintf(stderr, _("Status(DRAINING):\n"));
			snd_pcm_status_dump(status, log);
		}
		if (stream == SND_PCM_STREAM_CAPTURE) {
			fprintf(stderr, _("capture stream format change? attempting recover...\n"));
			if ((res = snd_pcm_prepare(handle))<0) {
				error(_("xrun(DRAINING): prepare error: %s"), snd_strerror(res));
				prg_exit(EXIT_FAILURE);
			}
			return;
		}
	}
	if (verbose) {
		fprintf(stderr, _("Status(R/W):\n"));
		snd_pcm_status_dump(status, log);
	}
	error(_("read/write error, state = %s"), snd_pcm_state_name(snd_pcm_status_get_state(status)));
	prg_exit(EXIT_FAILURE);
}

/* I/O suspend handler */
static void suspend(void)
{
	int res;

	if (!quiet_mode) {
		fprintf(stderr, _("Suspended. Trying resume. ")); fflush(stderr);
	}
	while ((res = snd_pcm_resume(handle)) == -EAGAIN)
		sleep(1);	/* wait until suspend flag is released */
	if (res < 0) {
		if (!quiet_mode) {
			fprintf(stderr, _("Failed. Restarting stream. ")); fflush(stderr);
		}
		if ((res = snd_pcm_prepare(handle)) < 0) {
			error(_("suspend: prepare error: %s"), snd_strerror(res));
			prg_exit(EXIT_FAILURE);
		}
	}
	if (!quiet_mode)
		fprintf(stderr, _("Done.\n"));
}

static void print_vu_meter_mono(int perc, int maxperc)
{
	const int bar_length = 50;
	char line[80];
	int val;

	for (val = 0; val <= perc * bar_length / 100 && val < bar_length; val++)
		line[val] = '#';
	for (; val <= maxperc * bar_length / 100 && val < bar_length; val++)
		line[val] = ' ';
	line[val] = '+';
	for (++val; val <= bar_length; val++)
		line[val] = ' ';
	if (maxperc > 99)
		sprintf(line + val, "| MAX");
	else
		sprintf(line + val, "| %02i%%", maxperc);
	fputs(line, stderr);
	if (perc > 100)
		fprintf(stderr, _(" !clip  "));
}

static void print_vu_meter_stereo(int *perc, int *maxperc)
{
	const int bar_length = 35;
	char line[80];
	int c;

	memset(line, ' ', sizeof(line) - 1);
	line[bar_length + 3] = '|';

	for (c = 0; c < 2; c++) {
		int p = perc[c] * bar_length / 100;
		char tmp[4];
		if (p > bar_length)
			p = bar_length;
		if (c)
			memset(line + bar_length + 6 + 1, '#', p);
		else
			memset(line + bar_length - p, '#', p);
		p = maxperc[c] * bar_length / 100 - 1;
		if (p < 0)
			p = 0;
		else if (p >= bar_length)
			p = bar_length - 1;
		if (c)
			line[bar_length + 6 + 1 + p] = '+';
		else
			line[bar_length - p - 1] = '+';
		if (ABS(maxperc[c]) > 99)
			sprintf(tmp, "MAX");
		else
			sprintf(tmp, "%02d%%", maxperc[c]);
		if (c)
			memcpy(line + bar_length + 3 + 1, tmp, 3);
		else
			memcpy(line + bar_length, tmp, 3);
	}
	line[bar_length * 2 + 6 + 2] = 0;
	fputs(line, stderr);
}

static void print_vu_meter(signed int *perc, signed int *maxperc)
{
	if (vumeter == VUMETER_STEREO)
		print_vu_meter_stereo(perc, maxperc);
	else
		print_vu_meter_mono(*perc, *maxperc);
}

/* peak handler */
static void compute_max_peak(u_char *data, size_t samples)
{
	signed int val, max, perc[2], max_peak[2];
	static int run = 0;
	size_t osamples = samples;
	int format_little_endian = snd_pcm_format_little_endian(hwparams.format);
	int ichans, c;

	if (vumeter == VUMETER_STEREO)
		ichans = 2;
	else
		ichans = 1;

	memset(max_peak, 0, sizeof(max_peak));
	switch (bits_per_sample) {
	case 8: {
		signed char *valp = (signed char *)data;
		signed char mask = snd_pcm_format_silence(hwparams.format);
		c = 0;
		while (samples-- > 0) {
			val = *valp++ ^ mask;
			val = abs(val);
			if (max_peak[c] < val)
				max_peak[c] = val;
			if (vumeter == VUMETER_STEREO)
				c = !c;
		}
		break;
	}
	case 16: {
		signed short *valp = (signed short *)data;
		signed short mask = snd_pcm_format_silence_16(hwparams.format);
		signed short sval;

		c = 0;
		while (samples-- > 0) {
			if (format_little_endian)
				sval = le16toh(*valp);
			else
				sval = be16toh(*valp);
			sval ^= mask;
			val = abs(sval);
			if (max_peak[c] < val)
				max_peak[c] = val;
			valp++;
			if (vumeter == VUMETER_STEREO)
				c = !c;
		}
		break;
	}
	case 24: {
		unsigned char *valp = data;
		signed int mask = snd_pcm_format_silence_32(hwparams.format);

		c = 0;
		while (samples-- > 0) {
			if (format_little_endian) {
				val = valp[0] | (valp[1]<<8) | (valp[2]<<16);
			} else {
				val = (valp[0]<<16) | (valp[1]<<8) | valp[2];
			}
			val ^= mask;
			/* Correct signed bit in 32-bit value */
			if (val & (1<<(bits_per_sample-1))) {
				val |= 0xff<<24;	/* Negate upper bits too */
			}
			val = abs(val);
			if (max_peak[c] < val)
				max_peak[c] = val;
			valp += 3;
			if (vumeter == VUMETER_STEREO)
				c = !c;
		}
		break;
	}
	case 32: {
		signed int *valp = (signed int *)data;
		signed int mask = snd_pcm_format_silence_32(hwparams.format);

		c = 0;
		while (samples-- > 0) {
			if (format_little_endian)
				val = le32toh(*valp);
			else
				val = be32toh(*valp);
			val ^= mask;
			if (val == 0x80000000U)
				val = 0x7fffffff;
			else
				val = abs(val);
			if (max_peak[c] < val)
				max_peak[c] = val;
			valp++;
			if (vumeter == VUMETER_STEREO)
				c = !c;
		}
		break;
	}
	default:
		if (run == 0) {
			fprintf(stderr, _("Unsupported bit size %d.\n"), (int)bits_per_sample);
			run = 1;
		}
		return;
	}
	max = 1 << (significant_bits_per_sample-1);
	if (max <= 0)
		max = 0x7fffffff;

	for (c = 0; c < ichans; c++) {
		if (max_peak[c] > max)
			max_peak[c] = max;
		if (bits_per_sample > 16)
			perc[c] = max_peak[c] / (max / 100);
		else
			perc[c] = max_peak[c] * 100 / max;
	}

	if (interleaved && verbose <= 2) {
		static int maxperc[2];
		static time_t t=0;
		const time_t tt=time(NULL);
		if(tt>t) {
			t=tt;
			maxperc[0] = 0;
			maxperc[1] = 0;
		}
		for (c = 0; c < ichans; c++)
			if (perc[c] > maxperc[c])
				maxperc[c] = perc[c];

		putc('\r', stderr);
		print_vu_meter(perc, maxperc);
		fflush(stderr);
	}
	else if (verbose==3) {
		fprintf(stderr, _("Max peak (%li samples): 0x%08x "), (long)osamples, max_peak[0]);
		for (val = 0; val < 20; val++)
			if (val <= perc[0] / 5)
				putc('#', stderr);
			else
				putc(' ', stderr);
		fprintf(stderr, " %i%%\n", perc[0]);
		fflush(stderr);
	}
}

static void do_test_position(void)
{
	static long counter = 0;
	static time_t tmr = -1;
	time_t now;
	static float availsum, delaysum, samples;
	static snd_pcm_sframes_t maxavail, maxdelay;
	static snd_pcm_sframes_t minavail, mindelay;
	static snd_pcm_sframes_t badavail = 0, baddelay = 0;
	snd_pcm_sframes_t outofrange;
	snd_pcm_sframes_t avail, delay, savail, sdelay;
	snd_pcm_status_t *status;
	int err;

	snd_pcm_status_alloca(&status);
	err = snd_pcm_avail_delay(handle, &avail, &delay);
	if (err < 0)
		return;
	err = snd_pcm_status(handle, status);
	if (err < 0)
		return;
	savail = snd_pcm_status_get_avail(status);
	sdelay = snd_pcm_status_get_delay(status);
	outofrange = (test_coef * (snd_pcm_sframes_t)buffer_frames) / 2;
	if (avail > outofrange || avail < -outofrange ||
	    delay > outofrange || delay < -outofrange) {
		badavail = avail; baddelay = delay;
		availsum = delaysum = samples = 0;
		maxavail = maxdelay = 0;
		minavail = mindelay = buffer_frames * 16;
		fprintf(stderr, _("Suspicious buffer position (%li total): "
			"avail = %li, delay = %li, buffer = %li\n"),
			++counter, (long)avail, (long)delay, (long)buffer_frames);
	} else if (savail > outofrange || savail < -outofrange ||
		   sdelay > outofrange || sdelay < -outofrange) {
		badavail = savail; baddelay = sdelay;
		availsum = delaysum = samples = 0;
		maxavail = maxdelay = 0;
		minavail = mindelay = buffer_frames * 16;
		fprintf(stderr, _("Suspicious status buffer position (%li total): "
			"avail = %li, delay = %li, buffer = %li\n"),
			++counter, (long)savail, (long)sdelay, (long)buffer_frames);
	} else if (stream == SND_PCM_STREAM_CAPTURE && avail > delay) {
		fprintf(stderr, _("Suspicious buffer position avail > delay (%li total): "
			"avail = %li, delay = %li\n"),
			++counter, (long)avail, (long)delay);
	} else if (stream == SND_PCM_STREAM_CAPTURE && savail > sdelay) {
		fprintf(stderr, _("Suspicious status buffer position avail > delay (%li total): "
			"avail = %li, delay = %li\n"),
			++counter, (long)savail, (long)sdelay);
	} else if (verbose) {
		time(&now);
		if (tmr == (time_t) -1) {
			tmr = now;
			availsum = delaysum = samples = 0;
			maxavail = maxdelay = 0;
			minavail = mindelay = buffer_frames * 16;
		}
		if (avail > maxavail)
			maxavail = avail;
		if (savail > maxavail)
			maxavail = savail;
		if (delay > maxdelay)
			maxdelay = delay;
		if (sdelay > maxdelay)
			maxdelay = sdelay;
		if (avail < minavail)
			minavail = avail;
		if (savail < minavail)
			minavail = savail;
		if (delay < mindelay)
			mindelay = delay;
		if (sdelay < mindelay)
			mindelay = sdelay;
		availsum += avail;
		delaysum += delay;
		samples++;
		if ((maxavail != 0 || maxdelay != 0) && now != tmr) {
			fprintf(stderr, "BUFPOS: avg%li/%li "
				"min%li/%li max%li/%li (%li) (%li:%li/%li)\n",
                         (long)(availsum / samples),
				(long)(delaysum / samples),
				(long)minavail, (long)mindelay,
				(long)maxavail, (long)maxdelay,
				(long)buffer_frames,
				counter, badavail, baddelay);
			tmr = now;
		}
	}
	if (verbose == 1) {
		fprintf(stderr, _("Status(R/W) (standalone avail=%li delay=%li):\n"), (long)avail, (long)delay);
		snd_pcm_status_dump(status, log);
	}
}

/*
 */
#ifdef CONFIG_SUPPORT_CHMAP
static u_char *remap_data(u_char *data, size_t count)
{
	static u_char *tmp, *src, *dst;
	static size_t tmp_size;
	size_t sample_bytes = bits_per_sample / 8;
	size_t step = bits_per_frame / 8;
	size_t chunk_bytes;
	unsigned int ch, i;

	if (!hw_map)
		return data;

	chunk_bytes = count * bits_per_frame / 8;
	if (tmp_size < chunk_bytes) {
		free(tmp);
		tmp = malloc(chunk_bytes);
		if (!tmp) {
			error(_("not enough memory"));
			exit(1);
		}
		tmp_size = count;
	}

	src = data;
	dst = tmp;
	for (i = 0; i < count; i++) {
		for (ch = 0; ch < hwparams.channels; ch++) {
			memcpy(dst, src + sample_bytes * hw_map[ch],
			       sample_bytes);
			dst += sample_bytes;
		}
		src += step;
	}
	return tmp;
}

static u_char **remap_datav(u_char **data, size_t count)
{
	static u_char **tmp;
	unsigned int ch;

	if (!hw_map)
		return data;

	if (!tmp) {
		tmp = malloc(sizeof(*tmp) * hwparams.channels);
		if (!tmp) {
			error(_("not enough memory"));
			exit(1);
		}
		for (ch = 0; ch < hwparams.channels; ch++)
			tmp[ch] = data[hw_map[ch]];
	}
	return tmp;
}
#else
#define remap_data(data, count)		(data)
#define remap_datav(data, count)	(data)
#endif

/*
 *  write function
 */

static ssize_t pcm_write(u_char *data, size_t count)
{
	ssize_t r;
	ssize_t result = 0;

	if (count < chunk_size) {
		snd_pcm_format_set_silence(hwparams.format, data + count * bits_per_frame / 8, (chunk_size - count) * hwparams.channels);
		count = chunk_size;
	}
	data = remap_data(data, count);
	while (count > 0 && !in_aborting) {
		if (test_position)
			do_test_position();
		check_stdin();
		r = writei_func(handle, data, count);
		if (test_position)
			do_test_position();
		if (r == -EAGAIN || (r >= 0 && (size_t)r < count)) {
			if (!test_nowait)
				snd_pcm_wait(handle, 100);
		} else if (r == -EPIPE) {
			xrun();
		} else if (r == -ESTRPIPE) {
			suspend();
		} else if (r < 0) {
			error(_("write error: %s"), snd_strerror(r));
			prg_exit(EXIT_FAILURE);
		}
		if (r > 0) {
			if (vumeter)
				compute_max_peak(data, r * hwparams.channels);
			result += r;
			count -= r;
			data += r * bits_per_frame / 8;
		}
	}
	return result;
}

static ssize_t pcm_writev(u_char **data, unsigned int channels, size_t count)
{
	ssize_t r;
	size_t result = 0;

	if (count != chunk_size) {
		unsigned int channel;
		size_t offset = count;
		size_t remaining = chunk_size - count;
		for (channel = 0; channel < channels; channel++)
			snd_pcm_format_set_silence(hwparams.format, data[channel] + offset * bits_per_sample / 8, remaining);
		count = chunk_size;
	}
	data = remap_datav(data, count);
	while (count > 0 && !in_aborting) {
		unsigned int channel;
		void *bufs[channels];
		size_t offset = result;
		for (channel = 0; channel < channels; channel++)
			bufs[channel] = data[channel] + offset * bits_per_sample / 8;
		if (test_position)
			do_test_position();
		check_stdin();
		r = writen_func(handle, bufs, count);
		if (test_position)
			do_test_position();
		if (r == -EAGAIN || (r >= 0 && (size_t)r < count)) {
			if (!test_nowait)
				snd_pcm_wait(handle, 100);
		} else if (r == -EPIPE) {
			xrun();
		} else if (r == -ESTRPIPE) {
			suspend();
		} else if (r < 0) {
			error(_("writev error: %s"), snd_strerror(r));
			prg_exit(EXIT_FAILURE);
		}
		if (r > 0) {
			if (vumeter) {
				for (channel = 0; channel < channels; channel++)
					compute_max_peak(data[channel], r);
			}
			result += r;
			count -= r;
		}
	}
	return result;
}

/*
 *  read function
 */

static ssize_t pcm_read(u_char *data, size_t rcount)
{
	ssize_t r;
	size_t result = 0;
	size_t count = rcount;

	if (count != chunk_size) {
		count = chunk_size;
	}

	while (count > 0) {
		if (in_aborting)
			goto abort;
		if (test_position)
			do_test_position();
		check_stdin();
		r = readi_func(handle, data, count);
		if (test_position)
			do_test_position();
		if (r == -EAGAIN || (r >= 0 && (size_t)r < count)) {
			if (!test_nowait)
				snd_pcm_wait(handle, 100);
		} else if (r == -EPIPE) {
			xrun();
		} else if (r == -ESTRPIPE) {
			suspend();
		} else if (r < 0) {
			error(_("read error: %s"), snd_strerror(r));
			prg_exit(EXIT_FAILURE);
		}
		if (r > 0) {
			if (vumeter)
				compute_max_peak(data, r * hwparams.channels);
			result += r;
			count -= r;
			data += r * bits_per_frame / 8;
		}
	}
abort:
	return rcount;
}

static ssize_t pcm_readv(u_char **data, unsigned int channels, size_t rcount)
{
	ssize_t r;
	size_t result = 0;
	size_t count = rcount;

	if (count != chunk_size) {
		count = chunk_size;
	}

	while (count > 0) {
		if (in_aborting)
			goto abort;
		unsigned int channel;
		void *bufs[channels];
		size_t offset = result;
		for (channel = 0; channel < channels; channel++)
			bufs[channel] = data[channel] + offset * bits_per_sample / 8;
		if (test_position)
			do_test_position();
		check_stdin();
		r = readn_func(handle, bufs, count);
		if (test_position)
			do_test_position();
		if (r == -EAGAIN || (r >= 0 && (size_t)r < count)) {
			if (!test_nowait)
				snd_pcm_wait(handle, 100);
		} else if (r == -EPIPE) {
			xrun();
		} else if (r == -ESTRPIPE) {
			suspend();
		} else if (r < 0) {
			error(_("readv error: %s"), snd_strerror(r));
			prg_exit(EXIT_FAILURE);
		}
		if (r > 0) {
			if (vumeter) {
				for (channel = 0; channel < channels; channel++)
					compute_max_peak(data[channel], r);
			}
			result += r;
			count -= r;
		}
	}
abort:
	return rcount;
}

/* setting the globals for playing raw data */
static void init_raw_data(void)
{
	hwparams = rhwparams;
}

/* calculate the data count to read from/to dsp */
static off64_t calc_count(void)
{
	off64_t count;

	if (timelimit == 0)
		if (sampleslimit == 0)
			count = pbrec_count;
		else
			count = snd_pcm_format_size(hwparams.format, sampleslimit * hwparams.channels);
	else {
		count = snd_pcm_format_size(hwparams.format, hwparams.rate * hwparams.channels);
		count *= (off64_t)timelimit;
	}
	return count < pbrec_count ? count : pbrec_count;
}

static void header(char *name)
{
	if (!quiet_mode) {
		if (! name)
			name = (stream == SND_PCM_STREAM_PLAYBACK) ? "stdout" : "stdin";
		fprintf(stderr, "%s raw '%s' : ",
			(stream == SND_PCM_STREAM_PLAYBACK) ? _("Playing") : _("Recording"),
			name);
		fprintf(stderr, "%s, ", snd_pcm_format_description(hwparams.format));
		fprintf(stderr, _("Rate %d Hz, "), hwparams.rate);
		if (hwparams.channels == 1)
			fprintf(stderr, _("Mono"));
		else if (hwparams.channels == 2)
			fprintf(stderr, _("Stereo"));
		else
			fprintf(stderr, _("Channels %i"), hwparams.channels);
		fprintf(stderr, "\n");
	}
}

/* playing raw data */

static void playback_go(int fd, size_t loaded, off64_t count, char *name)
{
	int l, r;
	off64_t written = 0;
	off64_t c;

	header(name);
	set_params();

	while (loaded > chunk_bytes && written < count && !in_aborting) {
		if (pcm_write(audiobuf + written, chunk_size) <= 0)
			return;
		written += chunk_bytes;
		loaded -= chunk_bytes;
	}
	if (written > 0 && loaded > 0)
		memmove(audiobuf, audiobuf + written, loaded);

	l = loaded;
	while (written < count && !in_aborting) {
		do {
			c = count - written;
			if (c > chunk_bytes)
				c = chunk_bytes;

			/* c < l, there is more data loaded
			 * then we actually need to write
			 */
			if (c < l)
				l = c;

			c -= l;

			if (c == 0)
				break;
			r = safe_read(fd, audiobuf + l, c);
			if (r < 0) {
				perror(name);
				prg_exit(EXIT_FAILURE);
			}
			fdcount += r;
			if (r == 0)
				break;
			l += r;
		} while ((size_t)l < chunk_bytes);
		l = l * 8 / bits_per_frame;
		r = pcm_write(audiobuf, l);
		if (r != l)
			break;
		r = r * bits_per_frame / 8;
		written += r;
		l = 0;
	}
	if (!in_aborting) {
		snd_pcm_nonblock(handle, 0);
		snd_pcm_drain(handle);
		snd_pcm_nonblock(handle, nonblock);
	}
}

static int playback_raw(char *name, int *loaded)
{
	init_raw_data();
	pbrec_count = calc_count();
	playback_go(fd, *loaded, pbrec_count, name);

	return 0;
}

/*
 *  let's play or capture it (capture_type says VOC/WAVE/raw)
 */

static void playback(char *name)
{
	int loaded = 0;

	pbrec_count = LLONG_MAX;
	fdcount = 0;
	if (!name || !strcmp(name, "-")) {
		fd = fileno(stdin);
		name = "stdin";
	} else {
		init_stdin();
		if ((fd = open(name, O_RDONLY, 0)) == -1) {
			perror(name);
			prg_exit(EXIT_FAILURE);
		}
	}

	playback_raw(name, &loaded);

	if (fd != fileno(stdin))
		close(fd);
}

/**
 * mystrftime
 *
 *   Variant of strftime(3) that supports additional format
 *   specifiers in the format string.
 *
 * Parameters:
 *
 *   s	  - destination string
 *   max	- max number of bytes to write
 *   userformat - format string
 *   tm	 - time information
 *   filenumber - the number of the file, starting at 1
 *
 * Returns: number of bytes written to the string s
 */
size_t mystrftime(char *s, size_t max, const char *userformat,
		  const struct tm *tm, const int filenumber)
{
	char formatstring[PATH_MAX] = "";
	char tempstring[PATH_MAX] = "";
	char *format, *tempstr;
	const char *pos_userformat;

	format = formatstring;

	/* if mystrftime is called with userformat = NULL we return a zero length string */
	if (userformat == NULL) {
		*s = '\0';
		return 0;
	}

	for (pos_userformat = userformat; *pos_userformat; ++pos_userformat) {
		if (*pos_userformat == '%') {
			tempstr = tempstring;
			tempstr[0] = '\0';
			switch (*++pos_userformat) {

				case '\0': // end of string
					--pos_userformat;
					break;

				case 'v': // file number 
					sprintf(tempstr, "%02d", filenumber);
					break;

				default: // All other codes will be handled by strftime
					*format++ = '%';
					*format++ = *pos_userformat;
					continue;
			}

			/* If a format specifier was found and used, copy the result. */
			if (tempstr[0]) {
				while ((*format = *tempstr++) != '\0')
					++format;
				continue;
			}
		}

		/* For any other character than % we simply copy the character */
		*format++ = *pos_userformat;
	}

	*format = '\0';
	format = formatstring;
	return strftime(s, max, format, tm);
}

static int new_capture_file(char *name, char *namebuf, size_t namelen,
			    int filecount)
{
	char *s;
	char buf[PATH_MAX-10];
	time_t t;
	struct tm *tmp;

	if (use_strftime) {
		t = time(NULL);
		tmp = localtime(&t);
		if (tmp == NULL) {
			perror("localtime");
			prg_exit(EXIT_FAILURE);
		}
		if (mystrftime(namebuf, namelen, name, tmp, filecount+1) == 0) {
			fprintf(stderr, "mystrftime returned 0");
			prg_exit(EXIT_FAILURE);
		}
		return filecount;
	}

	/* get a copy of the original filename */
	strncpy(buf, name, sizeof(buf));
	buf[sizeof(buf)-1] = '\0';

	/* separate extension from filename */
	s = buf + strlen(buf);
	while (s > buf && *s != '.' && *s != '/')
		--s;
	if (*s == '.')
		*s++ = 0;
	else if (*s == '/')
		s = buf + strlen(buf);

	/* upon first jump to this if block rename the first file */
	if (filecount == 1) {
		if (*s)
			snprintf(namebuf, namelen, "%s-01.%s", buf, s);
		else
			snprintf(namebuf, namelen, "%s-01", buf);
		remove(namebuf);
		rename(name, namebuf);
		filecount = 2;
	}

	/* name of the current file */
	if (*s)
		snprintf(namebuf, namelen, "%s-%02i.%s", buf, filecount, s);
	else
		snprintf(namebuf, namelen, "%s-%02i", buf, filecount);

	return filecount;
}

/**
 * create_path
 *
 *   This function creates a file path, like mkdir -p. 
 *
 * Parameters:
 *
 *   path - the path to create
 *
 * Returns: 0 on success, -1 on failure
 * On failure, a message has been printed to stderr.
 */
int create_path(const char *path)
{
	char *start;
	mode_t mode = S_IRWXU | S_IRGRP | S_IXGRP | S_IROTH | S_IXOTH;

	if (path[0] == '/')
		start = strchr(path + 1, '/');
	else
		start = strchr(path, '/');

	while (start) {
		char *buffer = strdup(path);
		buffer[start-path] = 0x00;

		if (mkdir(buffer, mode) == -1 && errno != EEXIST) {
			fprintf(stderr, "Problem creating directory %s", buffer);
			perror(" ");
			free(buffer);
			return -1;
		}
		free(buffer);
		start = strchr(start + 1, '/');
	}
	return 0;
}

static int safe_open(const char *name)
{
	int fd;

	fd = open(name, O_WRONLY | O_CREAT, 0644);
	if (fd == -1) {
		if (errno != ENOENT || !use_strftime)
			return -1;
		if (create_path(name) == 0)
			fd = open(name, O_WRONLY | O_CREAT, 0644);
	}
	return fd;
}

static void capture(char *orig_name)
{
	int tostdout=0;		/* boolean which describes output stream */
	int filecount=0;	/* number of files written */
	char *name = orig_name;	/* current filename */
	char namebuf[PATH_MAX+2];
	off64_t count, rest;		/* number of bytes to capture */
	struct stat statbuf;

	/* get number of bytes to capture */
	count = calc_count();
	if (count == 0)
		count = LLONG_MAX;
	/* compute the number of bytes per file */
	max_file_size = (long long) max_file_time *
		snd_pcm_format_size(hwparams.format,
				    hwparams.rate * hwparams.channels);
	/* WAVE-file should be even (I'm not sure), but wasting one byte
	   isn't a problem (this can only be in 8 bit mono) */
	if (count < LLONG_MAX)
		count += count % 2;
	else
		count -= count % 2;

	/* display verbose output to console */
	header(name);

	/* setup sound hardware */
	set_params();

	/* write to stdout? */
	if (!name || !strcmp(name, "-")) {
		fd = fileno(stdout);
		name = "stdout";
		tostdout = 1;
	}
	init_stdin();

	do {
		/* open a file to write */
		if (!tostdout) {
			/* upon the second file we start the numbering scheme */
			if (filecount || use_strftime) {
				filecount = new_capture_file(orig_name, namebuf,
							     sizeof(namebuf),
							     filecount);
				name = namebuf;
			}
			
			/* open a new file */
			if (!lstat(name, &statbuf)) {
				if (S_ISREG(statbuf.st_mode))
					remove(name);
			}
			fd = safe_open(name);
			if (fd < 0) {
				perror(name);
				prg_exit(EXIT_FAILURE);
			}
			filecount++;
		}

		rest = count;

		/* capture */
		fdcount = 0;
		while (rest > 0 && recycle_capture_file == 0 && !in_aborting) {
			size_t c = (rest <= (off64_t)chunk_bytes) ?
				(size_t)rest : chunk_bytes;
			size_t f = c * 8 / bits_per_frame;
			size_t read = pcm_read(audiobuf, f);
			size_t save;
			if (read != f)
				in_aborting = 1;
			save = read * bits_per_frame / 8;
			if (xwrite(fd, audiobuf, save) != save) {
				perror(name);
				in_aborting = 1;
				break;
			}
			count -= c;
			rest -= c;
			fdcount += c;
		}

		/* re-enable SIGUSR1 signal */
		if (recycle_capture_file) {
			recycle_capture_file = 0;
			signal(SIGUSR1, signal_handler_recycle);
		}

		/* finish sample container */
		if (!tostdout) {
			close(fd);
			fd = -1;
		}

		if (in_aborting)
			prg_exit(EXIT_FAILURE);

		/* repeat the loop when format is raw without timelimit or
		 * requested counts of data are recorded
		 */
	} while ((!timelimit && !sampleslimit) || count > 0);
}

static void playbackv_go(int* fds, unsigned int channels, size_t loaded, off64_t count, char **names)
{
	int r;
	size_t vsize;

	unsigned int channel;
	u_char *bufs[channels];

	header(names[0]);
	set_params();

	vsize = chunk_bytes / channels;

	// Not yet implemented
	assert(loaded == 0);

	for (channel = 0; channel < channels; ++channel)
		bufs[channel] = audiobuf + vsize * channel;

	while (count > 0 && !in_aborting) {
		size_t c = 0;
		size_t expected = count / channels;
		if (expected > vsize)
			expected = vsize;
		do {
			r = safe_read(fds[0], bufs[0], expected);
			if (r < 0) {
				perror(names[0]);
				prg_exit(EXIT_FAILURE);
			}
			for (channel = 1; channel < channels; ++channel) {
				if (safe_read(fds[channel], bufs[channel], r) != r) {
					perror(names[channel]);
					prg_exit(EXIT_FAILURE);
				}
			}
			if (r == 0)
				break;
			c += r;
		} while (c < expected);
		c = c * 8 / bits_per_sample;
		r = pcm_writev(bufs, channels, c);
		if ((size_t)r != c)
			break;
		r = r * bits_per_frame / 8;
		count -= r;
	}
	if (!in_aborting) {
		snd_pcm_nonblock(handle, 0);
		snd_pcm_drain(handle);
		snd_pcm_nonblock(handle, nonblock);
	}
}

static void capturev_go(int* fds, unsigned int channels, off64_t count, char **names)
{
	size_t c;
	ssize_t r;
	unsigned int channel;
	size_t vsize;
	u_char *bufs[channels];

	header(names[0]);
	set_params();

	vsize = chunk_bytes / channels;

	for (channel = 0; channel < channels; ++channel)
		bufs[channel] = audiobuf + vsize * channel;

	while (count > 0 && !in_aborting) {
		size_t rv;
		c = count;
		if (c > chunk_bytes)
			c = chunk_bytes;
		c = c * 8 / bits_per_frame;
		if ((size_t)(r = pcm_readv(bufs, channels, c)) != c)
			break;
		rv = r * bits_per_sample / 8;
		for (channel = 0; channel < channels; ++channel) {
			if ((size_t)xwrite(fds[channel], bufs[channel], rv) != rv) {
				perror(names[channel]);
				prg_exit(EXIT_FAILURE);
			}
		}
		r = r * bits_per_frame / 8;
		count -= r;
		fdcount += r;
	}
}

static void playbackv(char **names, unsigned int count)
{
	int ret = 0;
	unsigned int channel;
	unsigned int channels = rhwparams.channels;
	int alloced = 0;
	int fds[channels];
	for (channel = 0; channel < channels; ++channel)
		fds[channel] = -1;

	if (count == 1 && channels > 1) {
		size_t len = strlen(names[0]);
		char format[1024];
		memcpy(format, names[0], len);
		strcpy(format + len, ".%d");
		len += 4;
		names = malloc(sizeof(*names) * channels);
		for (channel = 0; channel < channels; ++channel) {
			names[channel] = malloc(len);
			sprintf(names[channel], format, channel);
		}
		alloced = 1;
	} else if (count != channels) {
		error(_("You need to specify %u files"), channels);
		prg_exit(EXIT_FAILURE);
	}

	for (channel = 0; channel < channels; ++channel) {
		fds[channel] = open(names[channel], O_RDONLY, 0);
		if (fds[channel] < 0) {
			perror(names[channel]);
			ret = EXIT_FAILURE;
			goto __end;
		}
	}
	/* should be raw data */
	init_raw_data();
	pbrec_count = calc_count();
	playbackv_go(fds, channels, 0, pbrec_count, names);

      __end:
	for (channel = 0; channel < channels; ++channel) {
		if (fds[channel] >= 0)
			close(fds[channel]);
		if (alloced)
			free(names[channel]);
	}
	if (alloced)
		free(names);
	if (ret)
		prg_exit(ret);
}

static void capturev(char **names, unsigned int count)
{
	int ret = 0;
	unsigned int channel;
	unsigned int channels = rhwparams.channels;
	int alloced = 0;
	int fds[channels];
	for (channel = 0; channel < channels; ++channel)
		fds[channel] = -1;

	if (count == 1) {
		size_t len = strlen(names[0]);
		char format[1024];
		memcpy(format, names[0], len);
		strcpy(format + len, ".%d");
		len += 4;
		names = malloc(sizeof(*names) * channels);
		for (channel = 0; channel < channels; ++channel) {
			names[channel] = malloc(len);
			sprintf(names[channel], format, channel);
		}
		alloced = 1;
	} else if (count != channels) {
		error(_("You need to specify %d files"), channels);
		prg_exit(EXIT_FAILURE);
	}

	for (channel = 0; channel < channels; ++channel) {
		fds[channel] = open(names[channel], O_WRONLY + O_CREAT, 0644);
		if (fds[channel] < 0) {
			perror(names[channel]);
			ret = EXIT_FAILURE;
			goto __end;
		}
	}
	/* should be raw data */
	init_raw_data();
	pbrec_count = calc_count();
	capturev_go(fds, channels, pbrec_count, names);

      __end:
	for (channel = 0; channel < channels; ++channel) {
		if (fds[channel] >= 0)
			close(fds[channel]);
		if (alloced)
			free(names[channel]);
	}
	if (alloced)
		free(names);
	if (ret)
		prg_exit(ret);
}
