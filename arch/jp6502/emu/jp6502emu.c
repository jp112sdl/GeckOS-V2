/*
 * jp6502emu - a small emulator of the JP6502 board, written to test the
 * GeckOS port before it goes into the flash.
 *
 * What it models:
 *
 *   $0000-$7fff  32k RAM
 *   $8080        TMS9918 (even address VRAM, odd address register)
 *   $8200        VIA3 - PS/2 keyboard controller on port A/CA1, SD card
 *                (bit-banged SPI) on port B
 *   $8400        R6551 ACIA, 19200 baud by default
 *   $8800        VIA2 - SN76489 (READY always low), LED on PB7, D-pad
 *   $9000        VIA1 - LCD (reads back "not busy"), DS3231 clock on I2C
 *                (PA0 = SCL, PA1 = SDA, pull-ups on the module)
 *   $a000-$ffff  ROM, the upper 24k of a 32k image
 *
 * The IRQ line is the wired-AND of the three VIAs and the ACIA, like on
 * the board.
 *
 * The CPU is a WDC 65C02 with the usual cycle counts. The chips are timed
 * off those cycles, so a timer that fires at 100 Hz on a 4 MHz board
 * fires every 40000 emulated cycles here too.
 *
 * Usage:
 *   jp6502emu [options] rom.bin
 *     -c MHZ        clock in MHz (default 4)
 *     -s FILE       SD card image (raw, 512-byte sectors); without one
 *                   the slot is empty and MISO stays high
 *     -z N          the card does not answer the first N CMD0, as some
 *                   cards do not right after power-up
 *     -d MS         the card takes MS milliseconds to find a block before
 *                   it sends the data token (up to 100 are allowed)
 *     -S            a strict card: while it still has to send part of an
 *                   answer - the CRC after a block, say - it does not listen
 *                   for a command; eight clocks with CS high end the answer
 *     -k TIME       the clock starts at TIME, "YYYY-MM-DD HH:MM[:SS]";
 *                   without it at the time of the host
 *     -K            the clock has never run: it starts at 2000-01-01 with
 *                   its oscillator-stopped flag set, as a new one does
 *     -R            no clock module: no pull-ups either, and the lines
 *                   keep the last level the VIA gave them (the bus holders
 *                   of the W65C22S)
 *     -x FILE       script, see below; without one the terminal is
 *                   connected to the ACIA (Ctrl-] quits)
 *     -t SECONDS    stop after this much emulated time
 *     -l FILE       label file from xa -l, for -T and the exit report
 *     -T            trace every instruction to stderr
 *     -v            report VDP accesses that come closer than 8 us
 *     -r            serial input at the baud rate even when the CPU does
 *                   not read it (overruns are counted, as on the board)
 *     -I            report the longest time with interrupts disabled
 *     -P            profile: cycles per label, all and with interrupts off
 *     -b ADDR       stop the run (and the script command) when PC gets
 *                   to ADDR (hex); "regs" and "peek" then show the state
 *
 * Script commands, one per line:
 *   wait SECONDS          run for that much emulated time
 *   ser TEXT              type TEXT into the ACIA (\r \n \t \\ \xNN)
 *   kbd TEXT              type TEXT on the PS/2 keyboard
 *   until TEXT [SECONDS]  run until the serial output contains TEXT
 *   screen                print the VDP text screen
 *   lcd                   print the LCD
 *   led                   print the LED state
 *   sound                 print the SN76489 volumes and the speaker
 *   rtc                   print the time of the clock
 *   regs                  print the CPU registers
 *   ilreset               restart the -I measurement and the overrun count
 *   jump ADDR [X]         continue at ADDR (hex), interrupts off, XR set
 *   quit                  stop
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <termios.h>
#include <fcntl.h>
#include <sys/select.h>
#include <time.h>

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

static double clock_mhz = 4.0;
static u64 cycles;
static u8 ram[0x8000];
static u8 rom[0x6000];

static int opt_trace, opt_vdpcheck, opt_realserial, opt_ilat;
static u64 ioff_since; static u16 ioff_pc;
static u64 ioff_max; static u16 ioff_max_from, ioff_max_to;
static int opt_prof;
static int opt_break = -1, break_hit;
#define ILRING 4096
static u16 ilring[ILRING]; static u8 ilflag[ILRING]; static unsigned ilpos;
static u16 ilmax_pcs[ILRING]; static unsigned ilmax_n;
static u64 prof[65536], prof_ioff[65536];
static long overruns;

/* ------------------------------------------------------------------ */
/* labels                                                              */

typedef struct { char name[48]; u16 addr; } label_t;
static label_t *labels;
static int nlabels;

static void load_labels(const char *fn)
{
	FILE *f = fopen(fn, "r");
	char line[256];
	if (!f) { perror(fn); return; }
	while (fgets(line, sizeof line, f)) {
		char name[128]; unsigned v;
		/* xa: "name, 0x1234, level, ..." */
		if (sscanf(line, "%127[^,], 0x%x", name, &v) == 2) {
			labels = realloc(labels, sizeof(label_t) * (nlabels + 1));
			snprintf(labels[nlabels].name, sizeof labels[0].name, "%s", name);
			labels[nlabels].addr = v;
			nlabels++;
		}
	}
	fclose(f);
}

static const char *label_for(u16 a, int *off)
{
	int best = -1; int bd = 1 << 20;
	for (int i = 0; i < nlabels; i++) {
		int d = a - labels[i].addr;
		if (d >= 0 && d < bd) { bd = d; best = i; }
	}
	if (best < 0 || bd > 512) return NULL;
	*off = bd;
	return labels[best].name;
}

/* ------------------------------------------------------------------ */
/* serial output capture                                               */

static char *serout;
static size_t serout_len, serout_cap;
static size_t serout_mark;	/* "until" searches from here */
static int interactive;

static void serial_out(u8 c)
{
	if (serout_len + 1 >= serout_cap) {
		serout_cap = serout_cap ? serout_cap * 2 : 65536;
		serout = realloc(serout, serout_cap);
	}
	serout[serout_len++] = c;
	serout[serout_len] = 0;
	if (c == '\r' && !interactive) return;
	putchar(c);
	fflush(stdout);
}

/* ------------------------------------------------------------------ */
/* VIA 6522                                                            */

typedef struct via {
	const char *name;
	u8 orb, ora, ddrb, ddra;
	u8 t1ll, t1lh, t2ll;
	u8 sr, acr, pcr, ifr, ier;
	int32_t t1c, t2c;
	int t1armed, t2armed;
	u8 pa_in, pb_in;	/* levels driven by the outside world */
	u8 (*read_pb)(struct via *);
	void (*write_pb)(struct via *);
	u8 (*read_pa)(struct via *);
} via_t;

static via_t via1 = { .name = "VIA1" }, via2 = { .name = "VIA2" }, via3 = { .name = "VIA3" };

static void via_reset(via_t *v)
{
	v->orb = v->ora = v->ddrb = v->ddra = 0;
	v->acr = v->pcr = v->ifr = v->ier = 0;
	v->t1c = v->t2c = 0xffff;
	v->t1armed = v->t2armed = 0;
	v->pa_in = v->pb_in = 0xff;
}

static int via_irq(via_t *v)
{
	return (v->ifr & v->ier & 0x7f) != 0;
}

static void via_tick(via_t *v, int n)
{
	/* T1 */
	v->t1c -= n;
	while (v->t1c < -1) {
		if (v->t1armed) {
			v->ifr |= 0x40;
			if (!(v->acr & 0x40))
				v->t1armed = 0;
			if (v->acr & 0x80)
				v->orb ^= 0x80;
		}
		if (v->acr & 0x40)
			v->t1c += (v->t1ll | (v->t1lh << 8)) + 2;
		else
			v->t1c += 0x10000;
	}
	/* T2 (timed mode only) */
	if (!(v->acr & 0x20)) {
		v->t2c -= n;
		while (v->t2c < -1) {
			if (v->t2armed) {
				v->ifr |= 0x20;
				v->t2armed = 0;
			}
			v->t2c += 0x10000;
		}
	}
}

static u8 via_read(via_t *v, int r)
{
	u8 val;
	switch (r) {
	case 0:
		v->ifr &= ~0x18;
		{
			u8 pins = v->read_pb ? v->read_pb(v) : v->pb_in;
			val = (v->orb & v->ddrb) | (pins & ~v->ddrb);
		}
		return val;
	case 1:
		v->ifr &= ~0x03;
		/* fall through */
	case 15:
		{
			u8 pins = v->read_pa ? v->read_pa(v) : v->pa_in;
			return (v->ora & v->ddra) | (pins & ~v->ddra);
		}
	case 2: return v->ddrb;
	case 3: return v->ddra;
	case 4: v->ifr &= ~0x40; return v->t1c & 0xff;
	case 5: return (v->t1c >> 8) & 0xff;
	case 6: return v->t1ll;
	case 7: return v->t1lh;
	case 8: v->ifr &= ~0x20; return v->t2c & 0xff;
	case 9: return (v->t2c >> 8) & 0xff;
	case 10: v->ifr &= ~0x04; return v->sr;
	case 11: return v->acr;
	case 12: return v->pcr;
	case 13: return v->ifr | (via_irq(v) ? 0x80 : 0);
	case 14: return v->ier | 0x80;
	}
	return 0xff;
}

static void via_write(via_t *v, int r, u8 d)
{
	switch (r) {
	case 0: v->orb = d; v->ifr &= ~0x18; if (v->write_pb) v->write_pb(v); break;
	case 1: v->ora = d; v->ifr &= ~0x03; break;
	case 15: v->ora = d; break;
	case 2: v->ddrb = d; if (v->write_pb) v->write_pb(v); break;
	case 3: v->ddra = d; break;
	case 4: case 6: v->t1ll = d; break;
	case 5:
		v->t1lh = d;
		v->t1c = v->t1ll | (d << 8);
		v->ifr &= ~0x40;
		v->t1armed = 1;
		if (v->acr & 0x80) v->orb &= ~0x80;
		break;
	case 7: v->t1lh = d; v->ifr &= ~0x40; break;
	case 8: v->t2ll = d; break;
	case 9:
		v->t2c = v->t2ll | (d << 8);
		v->ifr &= ~0x20;
		v->t2armed = 1;
		break;
	case 10: v->sr = d; v->ifr &= ~0x04; break;
	case 11: v->acr = d; break;
	case 12: v->pcr = d; break;
	case 13: v->ifr &= ~(d & 0x7f); break;
	case 14:
		if (d & 0x80) v->ier |= d & 0x7f;
		else v->ier &= ~(d & 0x7f);
		break;
	}
}

/* CA1 edge from the outside */
static void via_ca1(via_t *v, int level)
{
	static int last = 1;
	int pos = v->pcr & 1;
	if ((pos && !last && level) || (!pos && last && !level))
		v->ifr |= 0x02;
	last = level;
}

/* ------------------------------------------------------------------ */
/* ACIA 6551                                                           */

static struct {
	u8 rdr, cmd, ctrl, status;	/* status: bit3 RDRF, bit4 TDRE, bit2 OVR */
	int irqflag;
	u64 tx_done;		/* cycle when the shift register is empty */
	int tx_pending; u8 tx_hold;
	u64 rx_next;
	u8 *rxq; size_t rxq_len, rxq_pos;
} acia;

static double baud_of(u8 ctrl)
{
	static const double tab[16] = { 115200/16.0*16, 50, 75, 109.92, 134.58, 150, 300, 600,
		1200, 1800, 2400, 3600, 4800, 7200, 9600, 19200 };
	return tab[ctrl & 15];
}

static u64 char_cycles(void)
{
	double b = baud_of(acia.ctrl);
	return (u64)(clock_mhz * 1e6 * 10.0 / b);
}

static void acia_reset(void)
{
	acia.cmd = 0; acia.ctrl = 0;
	acia.status = 0x10;
	acia.tx_pending = 0;
	acia.irqflag = 0;
}

static int acia_irq(void)
{
	int rxint = !(acia.cmd & 0x02) && (acia.cmd & 0x01);
	int txint = ((acia.cmd & 0x0c) == 0x04) && (acia.cmd & 0x01);
	if (rxint && (acia.status & 0x08)) return 1;
	if (txint && (acia.status & 0x10)) return 1;
	return 0;
}

static void acia_queue(const u8 *s, size_t n)
{
	acia.rxq = realloc(acia.rxq, acia.rxq_len + n + 1);
	memcpy(acia.rxq + acia.rxq_len, s, n);
	acia.rxq_len += n;
}

static void acia_tick(void)
{
	/* transmit: the shift register finished */
	if (cycles >= acia.tx_done && acia.tx_done) {
		/* char was already put out when it started; nothing here */
	}
	if (acia.tx_pending && cycles >= acia.tx_done) {
		serial_out(acia.tx_hold);
		acia.tx_pending = 0;
		acia.tx_done = cycles + char_cycles();
		acia.status |= 0x10;
	}
	/* receive - with -r at the baud rate whether the CPU keeps up or
	   not, like the host would send; otherwise only when RDR is free */
	if (acia.rxq_pos < acia.rxq_len && cycles >= acia.rx_next &&
	    (opt_realserial || !(acia.status & 0x08))) {
		if (acia.status & 0x08) {
			overruns++;
			acia.status |= 0x04;
		}
		acia.rdr = acia.rxq[acia.rxq_pos++];
		acia.status |= 0x08;
		{
			/* back to back while the host has more, from now after a pause */
			u64 base = acia.rx_next;
			if (!opt_realserial || cycles > acia.rx_next + char_cycles())
				base = cycles;
			acia.rx_next = base + char_cycles();
		}
	}
}

static u8 acia_read(int r)
{
	switch (r) {
	case 0:
		acia.status &= ~0x0c;
		return acia.rdr;
	case 1: {
		u8 s = acia.status | (acia_irq() ? 0x80 : 0);
		return s;
	}
	case 2: return acia.cmd;
	case 3: return acia.ctrl;
	}
	return 0;
}

static void acia_write(int r, u8 d)
{
	switch (r) {
	case 0:
		if (cycles >= acia.tx_done && !acia.tx_pending) {
			/* straight into the shift register */
			serial_out(d);
			acia.tx_done = cycles + char_cycles();
			acia.status |= 0x10;
		} else {
			acia.tx_hold = d;
			acia.tx_pending = 1;
			acia.status &= ~0x10;
		}
		break;
	case 1:		/* programmed reset */
		acia.cmd &= 0xe0;
		acia.status &= ~0x04;
		break;
	case 2: acia.cmd = d; break;
	case 3: acia.ctrl = d; break;
	}
}

/* ------------------------------------------------------------------ */
/* TMS9918                                                             */

static struct {
	u8 vram[16384];
	u8 reg[8];
	u16 addr;
	int latch; u8 first;
	u8 readahead;
	u8 status;
	u64 last_access;
	long violations;
	u64 frame_next;
} vdp;

static void vdp_check(void)
{
	if (opt_vdpcheck && vdp.last_access) {
		double us = (cycles - vdp.last_access) / clock_mhz;
		if (us < 8.0) {
			vdp.violations++;
		}
	}
	vdp.last_access = cycles;
}

static u8 vdp_read(int port)
{
	vdp_check();
	if (port & 1) {
		u8 s = vdp.status;
		vdp.status &= 0x1f;
		vdp.latch = 0;
		return s;
	}
	u8 v = vdp.readahead;
	vdp.readahead = vdp.vram[vdp.addr & 0x3fff];
	vdp.addr = (vdp.addr + 1) & 0x3fff;
	vdp.latch = 0;
	return v;
}

static void vdp_write(int port, u8 d)
{
	vdp_check();
	if (port & 1) {
		if (!vdp.latch) {
			vdp.first = d;
			vdp.latch = 1;
		} else {
			vdp.latch = 0;
			if (d & 0x80) {
				vdp.reg[d & 7] = vdp.first;
			} else {
				vdp.addr = (vdp.first | (d << 8)) & 0x3fff;
				if (!(d & 0x40)) {
					vdp.readahead = vdp.vram[vdp.addr];
					vdp.addr = (vdp.addr + 1) & 0x3fff;
				}
			}
		}
	} else {
		vdp.vram[vdp.addr & 0x3fff] = d;
		vdp.readahead = d;
		vdp.addr = (vdp.addr + 1) & 0x3fff;
		vdp.latch = 0;
	}
}

static void vdp_tick(void)
{
	if (cycles >= vdp.frame_next) {
		vdp.frame_next = cycles + (u64)(clock_mhz * 1e6 / 60);
		vdp.status |= 0x80;
	}
}

static void vdp_screen(FILE *f)
{
	int text = (vdp.reg[1] & 0x18) == 0x10;
	int cols = text ? 40 : 32;
	u16 nt = (vdp.reg[2] & 0x0f) * 0x400;
	fprintf(f, "+----------------------------------------+ VDP %s%s, colours %d on %d\n",
		text ? "text" : "graphics", (vdp.reg[1] & 0x40) ? "" : " (blank)",
		vdp.reg[7] >> 4, vdp.reg[7] & 15);
	for (int r = 0; r < 24; r++) {
		fputc('|', f);
		for (int c = 0; c < cols; c++) {
			u8 ch = vdp.vram[(nt + r * cols + c) & 0x3fff];
			if (ch & 0x80) ch = '#';	/* inverse (cursor) */
			fputc(ch >= 32 && ch < 127 ? ch : '.', f);
		}
		fputs("|\n", f);
	}
	fprintf(f, "+----------------------------------------+\n");
	if (opt_vdpcheck)
		fprintf(f, "VDP accesses closer than 8 us: %ld\n", vdp.violations);
}

/* ------------------------------------------------------------------ */
/* keyboard controller on VIA3 port A / CA1                            */

static u8 *kbq; static size_t kbq_len, kbq_pos;
static u64 kb_next;

static void kbd_queue(const u8 *s, size_t n)
{
	kbq = realloc(kbq, kbq_len + n + 1);
	memcpy(kbq + kbq_len, s, n);
	kbq_len += n;
}

static void kbd_tick(void)
{
	if (kbq_pos < kbq_len && cycles >= kb_next && !(via3.ifr & 0x02)) {
		via3.pa_in = kbq[kbq_pos++];
		/* the controller pulls DATA_READY low for 2 ms */
		via_ca1(&via3, 0);
		via_ca1(&via3, 1);
		kb_next = cycles + (u64)(clock_mhz * 1e6 * 0.005);
	}
}

/* ------------------------------------------------------------------ */
/* SD card on VIA3 port B: CS bit 1, SCK bit 2, MOSI bit 3, MISO bit 4  */

#define SD_CS   0x02
#define SD_SCK  0x04
#define SD_MOSI 0x08
#define SD_MISO 0x10

static struct {
	FILE *img;
	u8 lastpb;
	u8 inbyte; int incount;
	u8 outbyte; int miso;
	u8 cmd[6]; int cmdlen;
	u8 resp[1024]; int resp_len, resp_pos;
	int app, idle_count, ready;
	int cmd0_skip;		/* -z: CMD0s still to be ignored */
	double read_ms;		/* -d: time until the data token of a read */
	int tok_pos; u64 tok_at;	/* where the token is in resp, and when */
	int strict;		/* -S */
	int oblig;		/* resp up to here has to be clocked out */
	int busy_byte;		/* the byte going out now is one of those */
	int hiclk;		/* clocks with CS high since it went high */
	/* write */
	int wr_state; u32 wr_block; int wr_count; u8 wr_buf[514];
	long reads, writes;
} sd;

static void sd_respond(const u8 *b, int n)
{
	memcpy(sd.resp + sd.resp_len, b, n);
	sd.resp_len += n;
}

static void sd_command(void)
{
	u8 c = sd.cmd[0] & 0x3f;
	u32 arg = (sd.cmd[1] << 24) | (sd.cmd[2] << 16) | (sd.cmd[3] << 8) | sd.cmd[4];
	u8 ff = 0xff;
	sd.resp_len = sd.resp_pos = 0;
	sd.tok_pos = -1;
	sd_respond(&ff, 1);	/* Ncr */
	int app = sd.app; sd.app = 0;
	u8 r1 = sd.ready ? 0x00 : 0x01;
	if (app && c == 41) {
		if (++sd.idle_count >= 2) sd.ready = 1;
		r1 = sd.ready ? 0x00 : 0x01;
		sd_respond(&r1, 1);
		return;
	}
	switch (c) {
	case 0:
		if (sd.cmd0_skip > 0) { sd.cmd0_skip--; break; }	/* no R1 */
		sd.ready = 0; sd.idle_count = 0; r1 = 0x01; sd_respond(&r1, 1); break;
	case 8: { u8 r[5] = { r1, 0, 0, 1, sd.cmd[4] }; sd_respond(r, 5); break; }
	case 55: sd.app = 1; sd_respond(&r1, 1); break;
	case 58: { u8 r[5] = { r1, 0xc0, 0xff, 0x80, 0x00 }; sd_respond(r, 5); break; }
	case 16: case 13: { u8 r[2] = { r1, 0 }; sd_respond(r, c == 13 ? 2 : 1); break; }
	case 17: {
		u8 buf[512];
		memset(buf, 0, sizeof buf);
		if (sd.img) {
			fseek(sd.img, (long)arg * 512, SEEK_SET);
			if (fread(buf, 1, 512, sd.img) != 512) { /* past the end: zeros */ }
		}
		sd.reads++;
		u8 r[2] = { r1, 0xff };
		sd_respond(r, 2);
		sd.tok_pos = sd.resp_len;
		sd.tok_at = cycles + (u64)(sd.read_ms * clock_mhz * 1000);
		u8 tok = 0xfe;
		sd_respond(&tok, 1);
		sd_respond(buf, 512);
		u8 crc[2] = { 0, 0 };
		sd_respond(crc, 2);
		break;
	}
	case 24:
		sd_respond(&r1, 1);
		sd.wr_state = 1; sd.wr_block = arg; sd.wr_count = 0;
		break;
	default: { u8 r = 0x04 | (sd.ready ? 0 : 1); sd_respond(&r, 1); break; }
	}
}

static void sd_byte_in(u8 b)
{
	if (sd.strict && sd.busy_byte && sd.wr_state == 0)
		return;		/* still answering, not listening */
	if (sd.wr_state == 1) {		/* waiting for the data token */
		if (b == 0xfe) { sd.wr_state = 2; sd.wr_count = 0; }
		return;
	}
	if (sd.wr_state == 2) {
		sd.wr_buf[sd.wr_count++] = b;
		if (sd.wr_count == 514) {
			if (sd.img) {
				fseek(sd.img, (long)sd.wr_block * 512, SEEK_SET);
				fwrite(sd.wr_buf, 1, 512, sd.img);
				fflush(sd.img);
			}
			sd.writes++;
			sd.wr_state = 0;
			sd.resp_len = sd.resp_pos = 0;
			u8 r[6] = { 0x05, 0x00, 0x00, 0x00, 0xff, 0xff };
			sd_respond(r, 6);
			sd.oblig = sd.resp_len - 2;	/* response and busy */
		}
		return;
	}
	if (sd.cmdlen == 0 && (b & 0xc0) != 0x40)
		return;
	sd.cmd[sd.cmdlen++] = b;
	if (sd.cmdlen == 6) {
		sd.cmdlen = 0;
		sd_command();
		sd.oblig = sd.resp_len;
	}
}

static u8 sd_next_out(void)
{
	sd.busy_byte = sd.resp_pos < sd.oblig;
	if (sd.resp_pos == sd.tok_pos && cycles < sd.tok_at)
		return 0xff;	/* still looking for the block */
	if (sd.resp_pos < sd.resp_len)
		return sd.resp[sd.resp_pos++];
	return 0xff;
}

static void sd_pb_write(via_t *v)
{
	u8 pb = (v->orb & v->ddrb) | (0xff & ~v->ddrb);
	u8 last = sd.lastpb;
	sd.lastpb = pb;
	if (pb & SD_CS) {
		sd.incount = 0;
		sd.miso = 1;
		if (!(last & SD_CS)) sd.hiclk = 0;
		if (!(last & SD_SCK) && (pb & SD_SCK) && ++sd.hiclk == 8)
			sd.resp_pos = sd.resp_len;	/* the answer is over */
		return;
	}
	if ((last & SD_CS) && !(pb & SD_CS)) {
		/* selected: present the first bit */
		sd.incount = 0;
		sd.outbyte = sd_next_out();
		sd.miso = sd.outbyte >> 7;
	}
	if (!(last & SD_SCK) && (pb & SD_SCK)) {
		/* rising edge: sample */
		sd.inbyte = (sd.inbyte << 1) | ((pb & SD_MOSI) ? 1 : 0);
		if (++sd.incount == 8) {
			sd.incount = 0;
			sd_byte_in(sd.inbyte);
		}
	}
	if ((last & SD_SCK) && !(pb & SD_SCK)) {
		/* falling edge: shift out */
		if (sd.incount == 0)
			sd.outbyte = sd_next_out();
		sd.miso = (sd.outbyte >> (7 - sd.incount)) & 1;
	}
}

static u8 via3_read_pb(via_t *v)
{
	(void)v;
	u8 pins = 0xff;
	if (sd.img && !sd.miso) pins &= ~SD_MISO;	/* no card: pulled up */
	return pins;
}

/* ------------------------------------------------------------------ */
/* VIA2: SN76489 - data on port A, READY PB0, /WE PB1, /CE PB2;        */
/* D-pad on PB3-PB6, not pressed; CB2 switches the speaker             */

static struct {
	u8 vol[4];		/* 0 loudest, 15 off */
	u16 tone[3];
	int latch;		/* register of the last latch byte */
	u8 lastpb;
	u64 busy_until;		/* READY low until then */
	long writes, early;	/* early: data changed while it was busy */
	int nbeep;		/* tones on channel 0: start, end, divider */
	u64 beep_on[64], beep_off[64];
	u16 beep_div[64];
	u8 beep_heard[64];	/* the speaker was on */
	int spk;		/* speaker on */
	u64 spk_at;		/* when it went on last */
	int spk_loud;		/* channels that sounded then */
} sn;

/* The speaker is in series with a MOSFET, which CB2 drives through an
   inverter, CB2 pulled up: it is on only while CB2 is a manual output
   driven low, PCR bits 7-5 = 110. Until then the tone the chip comes up
   with is not heard - the chip starts with every volume at 0 here, the
   loudest. */
static int speaker_on(void)
{
	return (via2.pcr & 0xe0) == 0xc0;
}

static void via2_write_pcr(void)
{
	int on = speaker_on();
	if (on && !sn.spk) {
		sn.spk_at = cycles;
		sn.spk_loud = 0;
		for (int i = 0; i < 4; i++)
			if (sn.vol[i] != 15) sn.spk_loud++;
	}
	sn.spk = on;
}

static void sn_byte(u8 b)
{
	u8 old0 = sn.vol[0];
	if (b & 0x80) {
		sn.latch = (b >> 4) & 7;
		if (sn.latch & 1) sn.vol[sn.latch >> 1] = b & 15;
		else if ((sn.latch >> 1) < 3) sn.tone[sn.latch >> 1] = (sn.tone[sn.latch >> 1] & 0x3f0) | (b & 15);
	} else {
		if (sn.latch & 1) sn.vol[sn.latch >> 1] = b & 15;
		else if ((sn.latch >> 1) < 3) sn.tone[sn.latch >> 1] = (sn.tone[sn.latch >> 1] & 15) | ((b & 0x3f) << 4);
	}
	sn.writes++;
	if (old0 == 15 && sn.vol[0] != 15 && sn.nbeep < 64) {
		sn.beep_on[sn.nbeep] = cycles;
		sn.beep_div[sn.nbeep] = sn.tone[0];
		sn.beep_off[sn.nbeep] = 0;
		sn.beep_heard[sn.nbeep] = speaker_on();
		sn.nbeep++;
	}
	if (old0 != 15 && sn.vol[0] == 15 && sn.nbeep)
		sn.beep_off[sn.nbeep - 1] = cycles;
}

static void via2_write_pb(via_t *v)
{
	u8 pb = (v->orb & v->ddrb) | (0xff & ~v->ddrb);
	/* /WE falling with /CE low: the chip takes port A; 32 of its
	   clocks (about 9 us at 3.58 MHz) it is busy, READY low */
	if ((sn.lastpb & 0x02) && !(pb & 0x02) && !(pb & 0x04)) {
		sn_byte(v->ora & v->ddra);
		sn.busy_until = cycles + (u64)(9 * clock_mhz);
	}
	sn.lastpb = pb;
}

static void via2_write_pa(void)
{
	if (cycles < sn.busy_until) sn.early++;
}

static u8 via2_read_pb(via_t *v)
{
	(void)v;
	return cycles < sn.busy_until ? 0xfe : 0xff;
}

static void sn_print(FILE *f)
{
	fprintf(f, "SN76489 volume (15 = off): %d %d %d noise %d, %ld writes, "
		"%ld data changes while busy\n",
		sn.vol[0], sn.vol[1], sn.vol[2], sn.vol[3], sn.writes, sn.early);
	fprintf(f, "speaker %s", speaker_on() ? "on" : "off");
	if (sn.spk_at)
		fprintf(f, ", switched on at %.3fs with %d channels sounding",
			sn.spk_at / (clock_mhz * 1e6), sn.spk_loud);
	fprintf(f, "\n");
	/* the chip runs on the CPU oscillator */
	for (int i = 0; i < sn.nbeep; i++)
		fprintf(f, "  beep at %.3fs, %.0f ms, %.0f Hz%s\n",
			sn.beep_on[i] / (clock_mhz * 1e6),
			sn.beep_off[i] ? (sn.beep_off[i] - sn.beep_on[i]) / (clock_mhz * 1e3) : -1.0,
			sn.beep_div[i] ? clock_mhz * 1e6 / (32.0 * sn.beep_div[i]) : 0,
			sn.beep_heard[i] ? "" : ", speaker off");
}

/* ------------------------------------------------------------------ */
/* VIA1: HD44780 in 8-bit mode, data on PB, E=PA7 RW=PA6 RS=PA5        */

static struct {
	u8 ddram[128];
	u8 ac;
	u8 lastpa;
} lcd;

static void via1_write_pa_hook(void);

static u8 via1_read_pb(via_t *v)
{
	(void)v;
	/* reading: busy flag clear, address counter */
	return lcd.ac & 0x7f;
}

static void lcd_print(FILE *f)
{
	static const u8 base[4] = { 0x00, 0x40, 0x14, 0x54 };
	for (int r = 0; r < 4; r++) {
		fputs("LCD |", f);
		for (int c = 0; c < 20; c++) {
			u8 ch = lcd.ddram[(base[r] + c) & 0x7f];
			fputc(ch >= 32 && ch < 127 ? ch : ' ', f);
		}
		fputs("|\n", f);
	}
}

static void via1_write_pa_hook(void)
{
	u8 pa = via1.ora & via1.ddra;
	/* falling edge of E latches a write */
	if ((lcd.lastpa & 0x80) && !(pa & 0x80) && !(pa & 0x40)) {
		u8 d = via1.orb & via1.ddrb;
		if (pa & 0x20) {
			lcd.ddram[lcd.ac & 0x7f] = d;
			lcd.ac = (lcd.ac + 1) & 0x7f;
		} else if (d & 0x80) {
			lcd.ac = d & 0x7f;
		} else if (d == 0x01) {
			memset(lcd.ddram, ' ', sizeof lcd.ddram);
			lcd.ac = 0;
		} else if ((d & 0xfe) == 0x02) {
			lcd.ac = 0;
		}
	}
	lcd.lastpa = pa;
}

/* ------------------------------------------------------------------ */
/* DS3231 on I2C, VIA1 PA0 = SCL, PA1 = SDA                            */

/*
 * The lines follow every write to port A or its DDR; the clock looks at
 * them on each change, like the real one: START and STOP, a bit taken on
 * the rising edge of SCL, its own bits and acknowledges put out after the
 * falling one. The AT24C32 of the usual modules answers at its address
 * too, but keeps nothing.
 */

#define	RTC_I2C		0x68
#define	EEPROM_I2C	0x57

enum { I2C_IDLE, I2C_ADDR, I2C_WRITE, I2C_READ, I2C_OFF };

static struct {
	int present;		/* a module on the bus, with its pull-ups */
	int stopped;		/* -K */
	time_t base;		/* its time at base_cyc, the fields taken as UTC */
	u64 base_cyc;
	u8 reg[19];
	int scl, sda;		/* the levels on the lines */
	u8 hold;		/* without a module: what the bus holders keep */
	int st, n, dev, first, wrote, pull, fight;
	u8 sh, ptr, cur;
} rtc = { .present = 1, .scl = 1, .sda = 1, .hold = 3 };

static time_t rtc_now(void)
{
	return rtc.base + (time_t)((cycles - rtc.base_cyc) / (clock_mhz * 1e6));
}

static u8 tobcd(int v) { return (v / 10) << 4 | v % 10; }
static int frombcd(u8 b) { return (b >> 4) * 10 + (b & 15); }

/* a START copies the time into the registers that are read */
static void rtc_latch(void)
{
	time_t t = rtc_now();
	struct tm tm;
	gmtime_r(&t, &tm);
	rtc.reg[0] = tobcd(tm.tm_sec);
	rtc.reg[1] = tobcd(tm.tm_min);
	rtc.reg[2] = tobcd(tm.tm_hour);
	rtc.reg[3] = tm.tm_wday + 1;
	rtc.reg[4] = tobcd(tm.tm_mday);
	rtc.reg[5] = tobcd(tm.tm_mon + 1) | (tm.tm_year >= 200 ? 0x80 : 0);
	rtc.reg[6] = tobcd(tm.tm_year % 100);
}

/* the time registers were written: the clock goes on from there */
static void rtc_set(void)
{
	struct tm tm;
	memset(&tm, 0, sizeof tm);
	if (rtc.reg[2] & 0x40)
		fprintf(stderr, "\nDS3231: 12 hour mode is not modelled\n");
	tm.tm_sec = frombcd(rtc.reg[0] & 0x7f);
	tm.tm_min = frombcd(rtc.reg[1] & 0x7f);
	tm.tm_hour = frombcd(rtc.reg[2] & 0x3f);
	tm.tm_mday = frombcd(rtc.reg[4] & 0x3f);
	tm.tm_mon = frombcd(rtc.reg[5] & 0x1f) - 1;
	tm.tm_year = 100 + frombcd(rtc.reg[6]) + (rtc.reg[5] & 0x80 ? 100 : 0);
	rtc.base = timegm(&tm);
	rtc.base_cyc = cycles;
}

static u8 rtc_read(void)
{
	if (rtc.dev != RTC_I2C)
		return 0xff;
	if (rtc.ptr > 0x12)
		rtc.ptr = 0;
	if (rtc.ptr == 0)
		rtc_latch();
	return rtc.reg[rtc.ptr++];
}

static void rtc_write(u8 v)
{
	u8 r = rtc.ptr > 0x12 ? 0 : rtc.ptr;
	if (r <= 6) {
		rtc.reg[r] = v;
		rtc.wrote = 1;
	} else if (r == 0x0f) {
		/* OSF and the alarm flags can only be cleared */
		rtc.reg[r] = (rtc.reg[r] & v & 0x83) | (v & 0x08) | (rtc.reg[r] & 0x04);
	} else if (r < 0x11) {
		rtc.reg[r] = v;
	}
	rtc.ptr = r + 1;
}

static void rtc_update(void)
{
	u8 drv = via1.ddra & 3, lvl = via1.ora & drv;
	int scl, sda;
	if (rtc.present) {
		if (lvl && !rtc.fight) {
			rtc.fight = 1;
			fprintf(stderr, "\nDS3231: VIA1 drives an I2C line high\n");
		}
		scl = drv & 1 ? lvl & 1 : 1;
		sda = drv & 2 ? lvl >> 1 & 1 : 1;
		if (rtc.pull)
			sda = 0;
	} else {
		rtc.hold = (rtc.hold & ~drv) | lvl;
		scl = rtc.hold & 1;
		sda = rtc.hold >> 1 & 1;
	}
	int oscl = rtc.scl, osda = rtc.sda;
	rtc.scl = scl;
	rtc.sda = sda;
	if (!rtc.present)
		return;

	if (scl && oscl && sda != osda) {
		if (rtc.wrote)
			rtc_set();
		rtc.wrote = 0;
		rtc.pull = 0;
		if (!sda) {			/* START */
			rtc_latch();
			rtc.st = I2C_ADDR;
			rtc.n = 0;
		} else {			/* STOP */
			rtc.st = I2C_IDLE;
		}
		return;
	}
	if (scl && !oscl) {
		if (++rtc.n <= 8) {
			if (rtc.st == I2C_ADDR || rtc.st == I2C_WRITE)
				rtc.sh = rtc.sh << 1 | sda;
		} else if (rtc.st == I2C_READ && sda) {
			rtc.st = I2C_OFF;	/* not acknowledged: that was all */
		}
	} else if (!scl && oscl) {
		if (rtc.n == 8) {
			switch (rtc.st) {
			case I2C_ADDR:
				rtc.dev = rtc.sh >> 1;
				if (rtc.dev == RTC_I2C || rtc.dev == EEPROM_I2C) {
					rtc.pull = 1;
					rtc.first = 1;
				} else {
					rtc.st = I2C_OFF;
				}
				break;
			case I2C_WRITE:
				if (rtc.dev == RTC_I2C) {
					if (rtc.first)
						rtc.ptr = rtc.sh;
					else
						rtc_write(rtc.sh);
				}
				rtc.first = 0;
				rtc.pull = 1;
				break;
			case I2C_READ:
				rtc.pull = 0;	/* for the master's acknowledge */
				break;
			}
		} else if (rtc.n == 9) {
			rtc.n = 0;
			rtc.pull = 0;
			if (rtc.st == I2C_ADDR)
				rtc.st = rtc.sh & 1 ? I2C_READ : I2C_WRITE;
			if (rtc.st == I2C_READ) {
				rtc.cur = rtc_read();
				rtc.pull = !(rtc.cur & 0x80);
			}
		} else if (rtc.st == I2C_READ && rtc.n < 8) {
			rtc.pull = !(rtc.cur & (0x80 >> rtc.n));
		}
		rtc.sda = rtc.pull ? 0 : drv & 2 ? lvl >> 1 & 1 : 1;
	}
}

static u8 via1_read_pa(via_t *v)
{
	(void)v;
	return 0xfc | rtc.scl | rtc.sda << 1;
}

static void rtc_init(const char *when)
{
	struct tm tm;
	memset(&tm, 0, sizeof tm);
	if (rtc.stopped) {
		tm.tm_year = 100;
		tm.tm_mday = 1;
	} else if (when) {
		int y, mo, d, h, mi, sec = 0;
		if (sscanf(when, "%d-%d-%d %d:%d:%d", &y, &mo, &d, &h, &mi, &sec) < 5) {
			fprintf(stderr, "-k wants \"YYYY-MM-DD HH:MM[:SS]\"\n");
			exit(1);
		}
		tm.tm_year = y - 1900; tm.tm_mon = mo - 1; tm.tm_mday = d;
		tm.tm_hour = h; tm.tm_min = mi; tm.tm_sec = sec;
	} else {
		time_t t = time(NULL);
		localtime_r(&t, &tm);
	}
	rtc.base = timegm(&tm);
	rtc.base_cyc = cycles;
	rtc.reg[0x0e] = 0x1c;
	rtc.reg[0x0f] = rtc.stopped ? 0x88 : 0x08;
	rtc.reg[0x11] = 25;		/* degrees */
}

static void rtc_print(FILE *f)
{
	if (!rtc.present) {
		fprintf(f, "RTC none\n");
		return;
	}
	time_t t = rtc_now();
	struct tm tm;
	gmtime_r(&t, &tm);
	fprintf(f, "RTC %04d-%02d-%02d %02d:%02d:%02d%s\n", tm.tm_year + 1900,
		tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec,
		rtc.reg[0x0f] & 0x80 ? " (oscillator stopped flag)" : "");
}

/* ------------------------------------------------------------------ */
/* bus                                                                 */

static int led_state;

static u8 io_read(u16 a)
{
	if (a >= 0x8080 && a < 0x8100) return vdp_read(a & 1);
	if (a >= 0x8200 && a < 0x8400) return via_read(&via3, a & 15);
	if (a >= 0x8400 && a < 0x8800) return acia_read(a & 3);
	if (a >= 0x8800 && a < 0x9000) return via_read(&via2, a & 15);
	if (a >= 0x9000 && a < 0xa000) return via_read(&via1, a & 15);
	return 0xff;
}

static void io_write(u16 a, u8 d)
{
	if (a >= 0x8080 && a < 0x8100) { vdp_write(a & 1, d); return; }
	if (a >= 0x8200 && a < 0x8400) { via_write(&via3, a & 15, d); return; }
	if (a >= 0x8400 && a < 0x8800) { acia_write(a & 3, d); return; }
	if (a >= 0x8800 && a < 0x9000) {
		if ((a & 15) == 1 || (a & 15) == 15) via2_write_pa();
		via_write(&via2, a & 15, d);
		if ((a & 15) == 12) via2_write_pcr();
		led_state = ((via2.orb & via2.ddrb) & 0x80) != 0;
		return;
	}
	if (a >= 0x9000 && a < 0xa000) {
		via_write(&via1, a & 15, d);
		if ((a & 15) == 1 || (a & 15) == 15 || (a & 15) == 3) {
			via1_write_pa_hook();
			rtc_update();
		}
		return;
	}
}

static inline u8 rd(u16 a)
{
	if (a < 0x8000) return ram[a];
	if (a >= 0xa000) return rom[a - 0xa000];
	return io_read(a);
}

static inline void wr(u16 a, u8 d)
{
	if (a < 0x8000) { ram[a] = d; return; }
	if (a >= 0xa000) return;
	io_write(a, d);
}

/* ------------------------------------------------------------------ */
/* 65C02                                                               */

static u16 pc; static u8 A, X, Y, S, P;
#define FC 0x01
#define FZ 0x02
#define FI 0x04
#define FD 0x08
#define FB 0x10
#define FU 0x20
#define FV 0x40
#define FN 0x80

static int waiting, stopped;

static inline void setnz(u8 v) { P = (P & ~(FN | FZ)) | (v & FN) | (v ? 0 : FZ); }
static inline void push(u8 v) { ram[0x100 + S--] = v; }
static inline u8 pull(void) { return ram[0x100 + ++S]; }
static inline u16 rd16(u16 a) { return rd(a) | (rd(a + 1) << 8); }
static inline u16 rd16zp(u8 a) { return rd(a) | (rd((u8)(a + 1)) << 8); }

static const u8 cyc[256] = {
/*        0 1 2 3 4 5 6 7 8 9 A B C D E F */
/* 0 */   7,6,2,1,5,3,5,5,3,2,2,1,6,4,6,5,
/* 1 */   2,5,5,1,5,4,6,5,2,4,2,1,6,4,6,5,
/* 2 */   6,6,2,1,3,3,5,5,4,2,2,1,4,4,6,5,
/* 3 */   2,5,5,1,4,4,6,5,2,4,2,1,4,4,6,5,
/* 4 */   6,6,2,1,3,3,5,5,3,2,2,1,3,4,6,5,
/* 5 */   2,5,5,1,4,4,6,5,2,4,3,1,8,4,6,5,
/* 6 */   6,6,2,1,3,3,5,5,4,2,2,1,6,4,6,5,
/* 7 */   2,5,5,1,4,4,6,5,2,4,4,1,6,4,6,5,
/* 8 */   3,6,2,1,3,3,3,5,2,2,2,1,4,4,4,5,
/* 9 */   2,6,5,1,4,4,4,5,2,5,2,1,4,5,5,5,
/* A */   2,6,2,1,3,3,3,5,2,2,2,1,4,4,4,5,
/* B */   2,5,5,1,4,4,4,5,2,4,2,1,4,4,4,5,
/* C */   2,6,2,1,3,3,5,5,2,2,2,3,4,4,6,5,
/* D */   2,5,5,1,4,4,6,5,2,4,3,3,4,4,7,5,
/* E */   2,6,2,1,3,3,5,5,2,2,2,1,4,4,6,5,
/* F */   2,5,5,1,4,4,6,5,2,4,4,1,4,4,7,5,
};

static void adc(u8 v)
{
	if (P & FD) {
		int c = P & FC;
		int lo = (A & 15) + (v & 15) + c;
		int hi = (A >> 4) + (v >> 4);
		if (lo > 9) { lo += 6; hi++; }
		int bin = A + v + c;
		P &= ~(FV | FC);
		if (~(A ^ v) & (A ^ bin) & 0x80) P |= FV;
		if (hi > 9) { hi += 6; }
		if (hi > 15) P |= FC;
		A = ((hi << 4) | (lo & 15)) & 0xff;
		setnz(A);
	} else {
		int r = A + v + (P & FC);
		P &= ~(FV | FC);
		if (~(A ^ v) & (A ^ r) & 0x80) P |= FV;
		if (r > 255) P |= FC;
		A = r;
		setnz(A);
	}
}

static void sbc(u8 v)
{
	if (P & FD) {
		int c = (P & FC) ? 0 : 1;
		int bin = A - v - c;
		int lo = (A & 15) - (v & 15) - c;
		int hi = (A >> 4) - (v >> 4);
		if (lo < 0) { lo -= 6; hi--; }
		if (hi < 0) hi -= 6;
		P &= ~(FV | FC);
		if ((A ^ v) & (A ^ bin) & 0x80) P |= FV;
		if (bin >= 0) P |= FC;
		A = ((hi << 4) | (lo & 15)) & 0xff;
		setnz(A);
	} else {
		adc(~v);
	}
}

static inline void cmp(u8 r, u8 v)
{
	int t = r - v;
	P = (P & ~FC) | (t >= 0 ? FC : 0);
	setnz(t & 0xff);
}

static void irq_enter(u16 vec, int brk)
{
	push(pc >> 8); push(pc & 0xff);
	push((P | FU | (brk ? FB : 0)) & (brk ? 0xff : ~FB));
	P |= FI; P &= ~FD;
	pc = rd16(vec);
}

static void trace(void)
{
	int off; const char *l = label_for(pc, &off);
	fprintf(stderr, "%10llu %04X %02X %02X %02X  A=%02X X=%02X Y=%02X S=%02X P=%02X",
		(unsigned long long)cycles, pc, rd(pc), rd(pc + 1), rd(pc + 2), A, X, Y, S, P);
	if (l) fprintf(stderr, "  %s+%d", l, off);
	fputc('\n', stderr);
}

static int step(void)
{
	u8 op; u16 ea; u8 v; int extra = 0;

	if (stopped) return 1;
	if (opt_trace) trace();
	op = rd(pc++);

#define IMM   (ea = pc++)
#define ZP    (ea = rd(pc++))
#define ZPX   (ea = (u8)(rd(pc++) + X))
#define ZPY   (ea = (u8)(rd(pc++) + Y))
#define ABS   (ea = rd16(pc), pc += 2)
#define ABSX  (ea = rd16(pc) + X, extra = ((ea - X) ^ ea) >> 8 ? 1 : 0, pc += 2)
#define ABSY  (ea = rd16(pc) + Y, extra = ((ea - Y) ^ ea) >> 8 ? 1 : 0, pc += 2)
#define INDX  (ea = rd16zp((u8)(rd(pc++) + X)))
#define INDY  (ea = rd16zp(rd(pc++)), ea += Y, extra = ((ea - Y) ^ ea) >> 8 ? 1 : 0)
#define INDZ  (ea = rd16zp(rd(pc++)))
#define BR(c) { int8_t o = rd(pc++); if (c) { u16 n = pc + o; extra = 1 + (((n ^ pc) & 0xff00) ? 1 : 0); pc = n; } }

	switch (op) {
	/* ORA */
	case 0x09: IMM; A |= rd(ea); setnz(A); break;
	case 0x05: ZP;  A |= rd(ea); setnz(A); break;
	case 0x15: ZPX; A |= rd(ea); setnz(A); break;
	case 0x0d: ABS; A |= rd(ea); setnz(A); break;
	case 0x1d: ABSX; A |= rd(ea); setnz(A); break;
	case 0x19: ABSY; A |= rd(ea); setnz(A); break;
	case 0x01: INDX; A |= rd(ea); setnz(A); break;
	case 0x11: INDY; A |= rd(ea); setnz(A); break;
	case 0x12: INDZ; A |= rd(ea); setnz(A); break;
	/* AND */
	case 0x29: IMM; A &= rd(ea); setnz(A); break;
	case 0x25: ZP;  A &= rd(ea); setnz(A); break;
	case 0x35: ZPX; A &= rd(ea); setnz(A); break;
	case 0x2d: ABS; A &= rd(ea); setnz(A); break;
	case 0x3d: ABSX; A &= rd(ea); setnz(A); break;
	case 0x39: ABSY; A &= rd(ea); setnz(A); break;
	case 0x21: INDX; A &= rd(ea); setnz(A); break;
	case 0x31: INDY; A &= rd(ea); setnz(A); break;
	case 0x32: INDZ; A &= rd(ea); setnz(A); break;
	/* EOR */
	case 0x49: IMM; A ^= rd(ea); setnz(A); break;
	case 0x45: ZP;  A ^= rd(ea); setnz(A); break;
	case 0x55: ZPX; A ^= rd(ea); setnz(A); break;
	case 0x4d: ABS; A ^= rd(ea); setnz(A); break;
	case 0x5d: ABSX; A ^= rd(ea); setnz(A); break;
	case 0x59: ABSY; A ^= rd(ea); setnz(A); break;
	case 0x41: INDX; A ^= rd(ea); setnz(A); break;
	case 0x51: INDY; A ^= rd(ea); setnz(A); break;
	case 0x52: INDZ; A ^= rd(ea); setnz(A); break;
	/* ADC */
	case 0x69: IMM; adc(rd(ea)); break;
	case 0x65: ZP;  adc(rd(ea)); break;
	case 0x75: ZPX; adc(rd(ea)); break;
	case 0x6d: ABS; adc(rd(ea)); break;
	case 0x7d: ABSX; adc(rd(ea)); break;
	case 0x79: ABSY; adc(rd(ea)); break;
	case 0x61: INDX; adc(rd(ea)); break;
	case 0x71: INDY; adc(rd(ea)); break;
	case 0x72: INDZ; adc(rd(ea)); break;
	/* SBC */
	case 0xe9: IMM; sbc(rd(ea)); break;
	case 0xe5: ZP;  sbc(rd(ea)); break;
	case 0xf5: ZPX; sbc(rd(ea)); break;
	case 0xed: ABS; sbc(rd(ea)); break;
	case 0xfd: ABSX; sbc(rd(ea)); break;
	case 0xf9: ABSY; sbc(rd(ea)); break;
	case 0xe1: INDX; sbc(rd(ea)); break;
	case 0xf1: INDY; sbc(rd(ea)); break;
	case 0xf2: INDZ; sbc(rd(ea)); break;
	/* CMP */
	case 0xc9: IMM; cmp(A, rd(ea)); break;
	case 0xc5: ZP;  cmp(A, rd(ea)); break;
	case 0xd5: ZPX; cmp(A, rd(ea)); break;
	case 0xcd: ABS; cmp(A, rd(ea)); break;
	case 0xdd: ABSX; cmp(A, rd(ea)); break;
	case 0xd9: ABSY; cmp(A, rd(ea)); break;
	case 0xc1: INDX; cmp(A, rd(ea)); break;
	case 0xd1: INDY; cmp(A, rd(ea)); break;
	case 0xd2: INDZ; cmp(A, rd(ea)); break;
	case 0xe0: IMM; cmp(X, rd(ea)); break;
	case 0xe4: ZP;  cmp(X, rd(ea)); break;
	case 0xec: ABS; cmp(X, rd(ea)); break;
	case 0xc0: IMM; cmp(Y, rd(ea)); break;
	case 0xc4: ZP;  cmp(Y, rd(ea)); break;
	case 0xcc: ABS; cmp(Y, rd(ea)); break;
	/* LDA */
	case 0xa9: IMM; A = rd(ea); setnz(A); break;
	case 0xa5: ZP;  A = rd(ea); setnz(A); break;
	case 0xb5: ZPX; A = rd(ea); setnz(A); break;
	case 0xad: ABS; A = rd(ea); setnz(A); break;
	case 0xbd: ABSX; A = rd(ea); setnz(A); break;
	case 0xb9: ABSY; A = rd(ea); setnz(A); break;
	case 0xa1: INDX; A = rd(ea); setnz(A); break;
	case 0xb1: INDY; A = rd(ea); setnz(A); break;
	case 0xb2: INDZ; A = rd(ea); setnz(A); break;
	/* LDX */
	case 0xa2: IMM; X = rd(ea); setnz(X); break;
	case 0xa6: ZP;  X = rd(ea); setnz(X); break;
	case 0xb6: ZPY; X = rd(ea); setnz(X); break;
	case 0xae: ABS; X = rd(ea); setnz(X); break;
	case 0xbe: ABSY; X = rd(ea); setnz(X); break;
	/* LDY */
	case 0xa0: IMM; Y = rd(ea); setnz(Y); break;
	case 0xa4: ZP;  Y = rd(ea); setnz(Y); break;
	case 0xb4: ZPX; Y = rd(ea); setnz(Y); break;
	case 0xac: ABS; Y = rd(ea); setnz(Y); break;
	case 0xbc: ABSX; Y = rd(ea); setnz(Y); break;
	/* STA */
	case 0x85: ZP;  wr(ea, A); break;
	case 0x95: ZPX; wr(ea, A); break;
	case 0x8d: ABS; wr(ea, A); break;
	case 0x9d: ABSX; extra = 0; wr(ea, A); break;
	case 0x99: ABSY; extra = 0; wr(ea, A); break;
	case 0x81: INDX; wr(ea, A); break;
	case 0x91: INDY; extra = 0; wr(ea, A); break;
	case 0x92: INDZ; wr(ea, A); break;
	/* STX STY STZ */
	case 0x86: ZP;  wr(ea, X); break;
	case 0x96: ZPY; wr(ea, X); break;
	case 0x8e: ABS; wr(ea, X); break;
	case 0x84: ZP;  wr(ea, Y); break;
	case 0x94: ZPX; wr(ea, Y); break;
	case 0x8c: ABS; wr(ea, Y); break;
	case 0x64: ZP;  wr(ea, 0); break;
	case 0x74: ZPX; wr(ea, 0); break;
	case 0x9c: ABS; wr(ea, 0); break;
	case 0x9e: ABSX; extra = 0; wr(ea, 0); break;
	/* BIT */
	case 0x89: IMM; v = rd(ea); P = (P & ~FZ) | ((A & v) ? 0 : FZ); break;
	case 0x24: ZP;  v = rd(ea); goto bit;
	case 0x34: ZPX; v = rd(ea); goto bit;
	case 0x2c: ABS; v = rd(ea); goto bit;
	case 0x3c: ABSX; v = rd(ea);
	bit:	P = (P & ~(FN | FV | FZ)) | (v & (FN | FV)) | ((A & v) ? 0 : FZ); break;
	/* TSB TRB */
	case 0x04: ZP;  v = rd(ea); P = (P & ~FZ) | ((A & v) ? 0 : FZ); wr(ea, v | A); break;
	case 0x0c: ABS; v = rd(ea); P = (P & ~FZ) | ((A & v) ? 0 : FZ); wr(ea, v | A); break;
	case 0x14: ZP;  v = rd(ea); P = (P & ~FZ) | ((A & v) ? 0 : FZ); wr(ea, v & ~A); break;
	case 0x1c: ABS; v = rd(ea); P = (P & ~FZ) | ((A & v) ? 0 : FZ); wr(ea, v & ~A); break;
	/* shifts */
#define ASL(v) (P = (P & ~FC) | ((v) >> 7), (v) = (v) << 1, setnz(v))
#define LSR(v) (P = (P & ~FC) | ((v) & 1), (v) = (v) >> 1, setnz(v))
#define ROL(v) { u8 c = P & FC; P = (P & ~FC) | ((v) >> 7); (v) = ((v) << 1) | c; setnz(v); }
#define ROR(v) { u8 c = P & FC; P = (P & ~FC) | ((v) & 1); (v) = ((v) >> 1) | (c << 7); setnz(v); }
#define RMW(mode, OP) mode; v = rd(ea); OP(v); wr(ea, v); break;
	case 0x0a: ASL(A); break;
	case 0x06: RMW(ZP, ASL)
	case 0x16: RMW(ZPX, ASL)
	case 0x0e: RMW(ABS, ASL)
	case 0x1e: RMW(ABSX, ASL)
	case 0x4a: LSR(A); break;
	case 0x46: RMW(ZP, LSR)
	case 0x56: RMW(ZPX, LSR)
	case 0x4e: RMW(ABS, LSR)
	case 0x5e: RMW(ABSX, LSR)
	case 0x2a: ROL(A); break;
	case 0x26: ZP; v = rd(ea); ROL(v); wr(ea, v); break;
	case 0x36: ZPX; v = rd(ea); ROL(v); wr(ea, v); break;
	case 0x2e: ABS; v = rd(ea); ROL(v); wr(ea, v); break;
	case 0x3e: ABSX; v = rd(ea); ROL(v); wr(ea, v); break;
	case 0x6a: ROR(A); break;
	case 0x66: ZP; v = rd(ea); ROR(v); wr(ea, v); break;
	case 0x76: ZPX; v = rd(ea); ROR(v); wr(ea, v); break;
	case 0x6e: ABS; v = rd(ea); ROR(v); wr(ea, v); break;
	case 0x7e: ABSX; v = rd(ea); ROR(v); wr(ea, v); break;
	/* INC DEC */
	case 0x1a: A++; setnz(A); break;
	case 0x3a: A--; setnz(A); break;
	case 0xe6: ZP;  v = rd(ea) + 1; wr(ea, v); setnz(v); break;
	case 0xf6: ZPX; v = rd(ea) + 1; wr(ea, v); setnz(v); break;
	case 0xee: ABS; v = rd(ea) + 1; wr(ea, v); setnz(v); break;
	case 0xfe: ABSX; extra = 0; v = rd(ea) + 1; wr(ea, v); setnz(v); break;
	case 0xc6: ZP;  v = rd(ea) - 1; wr(ea, v); setnz(v); break;
	case 0xd6: ZPX; v = rd(ea) - 1; wr(ea, v); setnz(v); break;
	case 0xce: ABS; v = rd(ea) - 1; wr(ea, v); setnz(v); break;
	case 0xde: ABSX; extra = 0; v = rd(ea) - 1; wr(ea, v); setnz(v); break;
	case 0xe8: X++; setnz(X); break;
	case 0xca: X--; setnz(X); break;
	case 0xc8: Y++; setnz(Y); break;
	case 0x88: Y--; setnz(Y); break;
	/* transfers */
	case 0xaa: X = A; setnz(X); break;
	case 0x8a: A = X; setnz(A); break;
	case 0xa8: Y = A; setnz(Y); break;
	case 0x98: A = Y; setnz(A); break;
	case 0xba: X = S; setnz(X); break;
	case 0x9a: S = X; break;
	/* stack */
	case 0x48: push(A); break;
	case 0x68: A = pull(); setnz(A); break;
	case 0xda: push(X); break;
	case 0xfa: X = pull(); setnz(X); break;
	case 0x5a: push(Y); break;
	case 0x7a: Y = pull(); setnz(Y); break;
	case 0x08: push(P | FB | FU); break;
	case 0x28: P = pull() | FU; break;
	/* flags */
	case 0x18: P &= ~FC; break;
	case 0x38: P |= FC; break;
	case 0x58: P &= ~FI; break;
	case 0x78: P |= FI; break;
	case 0xb8: P &= ~FV; break;
	case 0xd8: P &= ~FD; break;
	case 0xf8: P |= FD; break;
	/* branches */
	case 0x10: BR(!(P & FN)); break;
	case 0x30: BR(P & FN); break;
	case 0x50: BR(!(P & FV)); break;
	case 0x70: BR(P & FV); break;
	case 0x90: BR(!(P & FC)); break;
	case 0xb0: BR(P & FC); break;
	case 0xd0: BR(!(P & FZ)); break;
	case 0xf0: BR(P & FZ); break;
	case 0x80: BR(1); break;
	/* jumps */
	case 0x4c: pc = rd16(pc); break;
	case 0x6c: pc = rd16(rd16(pc)); break;
	case 0x7c: pc = rd16(rd16(pc) + X); break;
	case 0x20: ea = rd16(pc); pc += 1; push(pc >> 8); push(pc & 0xff); pc = ea; break;
	case 0x60: pc = pull(); pc |= pull() << 8; pc++; break;
	case 0x40: P = pull() | FU; pc = pull(); pc |= pull() << 8; break;
	case 0x00: pc++; irq_enter(0xfffe, 1); break;
	case 0xea: break;
	case 0xcb: waiting = 1; break;
	case 0xdb: stopped = 1; break;
	default:
		/* RMB/SMB/BBR/BBS */
		if ((op & 0x0f) == 0x07) {
			ZP; v = rd(ea);
			if (op & 0x80) v |= 1 << ((op >> 4) & 7); else v &= ~(1 << ((op >> 4) & 7));
			wr(ea, v);
		} else if ((op & 0x0f) == 0x0f) {
			ZP; v = rd(ea);
			int bitset = (v >> ((op >> 4) & 7)) & 1;
			BR((op & 0x80) ? bitset : !bitset);
		} else {
			/* undefined: NOPs of various lengths */
			if ((op & 0x0f) == 0x02) pc++;
			else if (op == 0x44) pc++;
			else if (op == 0x54 || op == 0xd4 || op == 0xf4) pc++;
			else if (op == 0x5c || op == 0xdc || op == 0xfc) pc += 2;
		}
		break;
	}
	return cyc[op] + extra;
}

/* ------------------------------------------------------------------ */
/* system                                                              */

static void reset(void)
{
	via_reset(&via1); via_reset(&via2); via_reset(&via3);
	via3.read_pb = via3_read_pb;
	via3.write_pb = sd_pb_write;
	via2.read_pb = via2_read_pb;
	via2.write_pb = via2_write_pb;
	sn.lastpb = 0xff;
	sn.spk = 0;
	via1.read_pb = via1_read_pb;
	via1.read_pa = via1_read_pa;
	rtc_update();
	sd.lastpb = 0xff; sd.miso = 1;
	acia_reset();
	memset(lcd.ddram, ' ', sizeof lcd.ddram);
	S = 0xfd; P = FI | FU;
	pc = rd16(0xfffc);
	waiting = stopped = 0;
}

static int irq_line(void)
{
	return via_irq(&via1) || via_irq(&via2) || via_irq(&via3) || acia_irq();
}

static void run_cycles(u64 n)
{
	u64 end = cycles + n;
	while (cycles < end) {
		int c;
		u16 pc0 = pc;
		int wasoff = (P & FI) != 0;
		if (irq_line() && !(P & FI)) {
			waiting = 0;
			irq_enter(0xfffe, 0);
			c = 7;
		} else if (waiting || stopped) {
			if (irq_line()) waiting = 0;
			c = 4;
		} else {
			if (pc == opt_break && !break_hit) { break_hit = 1; return; }
			c = step();
		}
		cycles += c;
		if (opt_prof) {
			prof[pc0] += c;
			if (P & FI) prof_ioff[pc0] += c;
		}
		if (opt_ilat) {
			ilring[ilpos % ILRING] = pc0;
			ilflag[ilpos % ILRING] = P;
			ilpos++;
		}
		if (opt_ilat) {
			int off = (P & FI) != 0;
			static int armed;	/* not the boot, before the first cli */
			if (off && !wasoff) { ioff_since = cycles; ioff_pc = pc0; }
			if (!off && wasoff) {
				if (armed && cycles - ioff_since > ioff_max) {
					ioff_max = cycles - ioff_since;
					ioff_max_from = ioff_pc; ioff_max_to = pc0;
					/* keep the instructions of this window */
					ilmax_n = 0;
					for (unsigned k = ilpos > ILRING ? ilpos - ILRING : 0; k < ilpos; k++)
						ilmax_pcs[ilmax_n++] = ilring[k % ILRING];
				}
				armed = 1;
			}
		}
		via_tick(&via1, c); via_tick(&via2, c); via_tick(&via3, c);
		acia_tick();
		vdp_tick();
		kbd_tick();
	}
}

static u64 secs(double s) { return (u64)(s * clock_mhz * 1e6); }

/* decode \r \n \t \\ \xNN */
static size_t unescape(const char *s, u8 *out)
{
	size_t n = 0;
	while (*s) {
		if (*s == '\\' && s[1]) {
			s++;
			switch (*s) {
			case 'r': out[n++] = 13; break;
			case 'n': out[n++] = 10; break;
			case 't': out[n++] = 9; break;
			case 'e': out[n++] = 27; break;
			case 'b': out[n++] = 8; break;
			case '\\': out[n++] = '\\'; break;
			case 'x': { unsigned v; sscanf(s + 1, "%2x", &v); out[n++] = v; s += 2; break; }
			default: out[n++] = *s; break;
			}
			s++;
		} else {
			out[n++] = *s++;
		}
	}
	return n;
}

static void report(FILE *f)
{
	int off; const char *l = label_for(pc, &off);
	fprintf(f, "PC=%04X A=%02X X=%02X Y=%02X S=%02X P=%02X t=%.3fs", pc, A, X, Y, S, P,
		cycles / (clock_mhz * 1e6));
	if (l) fprintf(f, " (%s+%d)", l, off);
	fprintf(f, " SD reads=%ld writes=%ld LED=%s", sd.reads, sd.writes, led_state ? "on" : "off");
	if (opt_realserial) fprintf(f, " overruns=%ld", overruns);
	if (opt_ilat) {
		int o1, o2; const char *l1 = label_for(ioff_max_from, &o1), *l2 = label_for(ioff_max_to, &o2);
		fprintf(f, "\nlongest with interrupts off: %.0f us, from %04X (%s+%d) to %04X (%s+%d)",
			ioff_max / clock_mhz, ioff_max_from, l1 ? l1 : "?", l1 ? o1 : 0,
			ioff_max_to, l2 ? l2 : "?", l2 ? o2 : 0);
		FILE *t = fopen("ilat.trace", "w");
		if (t) {
			/* from the last time the window's start PC was seen */
			unsigned st = 0;
			for (unsigned k = 0; k < ilmax_n; k++) if (ilmax_pcs[k] == ioff_max_from) st = k;
			for (unsigned k = st; k < ilmax_n; k++) {
				int o; const char *l = label_for(ilmax_pcs[k], &o);
				fprintf(t, "%04X %s+%d\n", ilmax_pcs[k], l ? l : "?", o);
			}
			fclose(t);
		}
	}
	fputc('\n', f);
}

static int run_script(FILE *sf, double tmax)
{
	char line[4096];
	while (fgets(line, sizeof line, sf)) {
		line[strcspn(line, "\n")] = 0;
		if (!line[0] || line[0] == '#') continue;
		char *arg = strchr(line, ' ');
		if (arg) *arg++ = 0; else arg = "";
		if (!strcmp(line, "wait")) {
			run_cycles(secs(atof(arg)));
		} else if (!strcmp(line, "ser")) {
			u8 buf[4096]; size_t n = unescape(arg, buf);
			acia_queue(buf, n);
		} else if (!strcmp(line, "kbd")) {
			u8 buf[4096]; size_t n = unescape(arg, buf);
			kbd_queue(buf, n);
		} else if (!strcmp(line, "until")) {
			char pat[4096]; double to = 10.0;
			char *last = strrchr(arg, ' ');
			if (last && atof(last + 1) > 0) { to = atof(last + 1); *last = 0; }
			u8 raw[4096]; size_t n = unescape(arg, raw); raw[n] = 0;
			memcpy(pat, raw, n + 1);
			u64 end = cycles + secs(to);
			int found = 0;
			while (cycles < end) {
				run_cycles(secs(0.01));
				if (serout && strstr(serout + serout_mark, pat)) { found = 1; break; }
			}
			if (found) {
				serout_mark = strstr(serout + serout_mark, pat) - serout + strlen(pat);
			} else {
				fprintf(stderr, "\n*** until \"%s\" timed out after %.1fs\n", arg, to);
				report(stderr);
			}
		} else if (!strcmp(line, "screen")) {
			fflush(stdout);
			vdp_screen(stdout);
		} else if (!strcmp(line, "lcd")) {
			lcd_print(stdout);
		} else if (!strcmp(line, "sound")) {
			sn_print(stdout);
		} else if (!strcmp(line, "rtc")) {
			rtc_print(stdout);
		} else if (!strcmp(line, "led")) {
			printf("LED %s\n", led_state ? "on" : "off");
		} else if (!strcmp(line, "regs")) {
			report(stdout);
		} else if (!strcmp(line, "peek")) {
			unsigned a, n = 16;
			sscanf(arg, "%x %u", &a, &n);
			for (unsigned i = 0; i < n; i++) printf("%s%02X", i % 16 ? " " : (i ? "\n" : ""), rd(a + i));
			printf("\n");
		} else if (!strcmp(line, "jump")) {
			unsigned a, x = X;
			sscanf(arg, "%x %x", &a, &x);
			pc = a; X = x; P |= FI;
		} else if (!strcmp(line, "ilreset")) {
			ioff_max = 0; overruns = 0;
		} else if (!strcmp(line, "quit")) {
			return 0;
		} else {
			fprintf(stderr, "unknown script command %s\n", line);
		}
		if (tmax > 0 && cycles > secs(tmax)) break;
	}
	return 0;
}

static struct termios oldt;
static void restore_term(void) { tcsetattr(0, TCSANOW, &oldt); }

static void run_interactive(double tmax)
{
	struct termios t;
	interactive = 1;
	if (isatty(0)) {
		tcgetattr(0, &oldt);
		t = oldt;
		cfmakeraw(&t);
		tcsetattr(0, TCSANOW, &t);
		atexit(restore_term);
	}
	fprintf(stderr, "jp6502emu: serial console, Ctrl-] quits\r\n");
	for (;;) {
		run_cycles(secs(0.01));
		fd_set fds; FD_ZERO(&fds); FD_SET(0, &fds);
		struct timeval tv = { 0, 0 };
		if (select(1, &fds, NULL, NULL, &tv) > 0) {
			u8 buf[256];
			ssize_t n = read(0, buf, sizeof buf);
			if (n <= 0) break;
			for (ssize_t i = 0; i < n; i++)
				if (buf[i] == 0x1d) return;
			acia_queue(buf, n);
		}
		usleep(10000 / (clock_mhz > 0 ? 1 : 1));
		if (tmax > 0 && cycles > secs(tmax)) break;
	}
}

int main(int argc, char **argv)
{
	const char *script = NULL, *sdimg = NULL, *labfile = NULL, *rtctime = NULL;
	double tmax = 0;
	int o;
	while ((o = getopt(argc, argv, "c:s:x:t:l:TvrIPb:z:d:Sk:KR")) != -1) {
		switch (o) {
		case 'c': clock_mhz = atof(optarg); break;
		case 's': sdimg = optarg; break;
		case 'x': script = optarg; break;
		case 't': tmax = atof(optarg); break;
		case 'l': labfile = optarg; break;
		case 'T': opt_trace = 1; break;
		case 'v': opt_vdpcheck = 1; break;
		case 'r': opt_realserial = 1; break;
		case 'I': opt_ilat = 1; break;
		case 'P': opt_prof = 1; break;
		case 'b': opt_break = strtol(optarg, NULL, 16); break;
		case 'z': sd.cmd0_skip = atoi(optarg); break;
		case 'd': sd.read_ms = atof(optarg); break;
		case 'S': sd.strict = 1; break;
		case 'k': rtctime = optarg; break;
		case 'K': rtc.stopped = 1; break;
		case 'R': rtc.present = 0; break;
		default:
			fprintf(stderr, "usage: %s [-c MHz] [-s sd.img] [-z N] [-d ms] [-S] [-k time] [-K] [-R] [-x script] [-t secs] [-l labels] [-T] [-v] [-r] rom.bin\n", argv[0]);
			return 1;
		}
	}
	if (optind >= argc) { fprintf(stderr, "no ROM image\n"); return 1; }
	FILE *f = fopen(argv[optind], "rb");
	if (!f) { perror(argv[optind]); return 1; }
	u8 img[0x8000];
	size_t n = fread(img, 1, sizeof img, f);
	fclose(f);
	if (n == 0x8000) memcpy(rom, img + 0x2000, 0x6000);
	else if (n == 0x6000) memcpy(rom, img, 0x6000);
	else { fprintf(stderr, "ROM image must be 24k or 32k, is %zu\n", n); return 1; }
	if (sdimg) {
		sd.img = fopen(sdimg, "r+b");
		if (!sd.img) { perror(sdimg); return 1; }
	}
	if (labfile) load_labels(labfile);
	rtc_init(rtctime);
	for (int i = 0; i < 0x8000; i++) ram[i] = (i * 7 + 13) & 0xff;	/* not zero */
	reset();

	if (script) {
		FILE *sf = fopen(script, "r");
		if (!sf) { perror(script); return 1; }
		run_script(sf, tmax);
		fclose(sf);
	} else if (tmax > 0 && !isatty(0)) {
		/* batch: feed stdin to the ACIA and run */
		u8 buf[65536]; size_t k = fread(buf, 1, sizeof buf, stdin);
		acia_queue(buf, k);
		run_cycles(secs(tmax));
	} else {
		run_interactive(tmax);
	}
	fflush(stdout);
	fprintf(stderr, "\n");
	report(stderr);
	if (opt_prof) {
		/* sum per label */
		static u64 sum[65536], sumi[65536];
		for (int a = 0; a < 65536; a++) {
			if (!prof[a]) continue;
			int off; const char *l = label_for(a, &off);
			int key = l ? a - off : a;
			sum[key] += prof[a]; sumi[key] += prof_ioff[a];
		}
		for (int pass = 0; pass < 2; pass++) {
			u64 *t = pass ? sumi : sum;
			fprintf(stderr, pass ? "top, interrupts off:\n" : "top, all:\n");
			for (int n = 0; n < 25; n++) {
				int best = -1;
				for (int a = 0; a < 65536; a++) if (t[a] && (best < 0 || t[a] > t[best])) best = a;
				if (best < 0) break;
				int off; const char *l = label_for(best, &off);
				fprintf(stderr, "  %04X %-16s %12llu\n", best, l ? l : "?", (unsigned long long)t[best]);
				t[best] = 0;
			}
		}
	}
	return 0;
}
