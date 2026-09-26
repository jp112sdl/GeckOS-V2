
# GeckOS for the JP6502 board
#
#   make		ROM image boot/geckos.bin (32k, for the flash tool)
#   make CLOCK=2	for another CPU clock (1, 2, 4 or 8 MHz; default 4)
#   make SHELLS=-DNO_SERIAL_SHELL	only the shell on the VDP console
#   make SHELLS=-DNO_VIDEO_SHELL	only the shell on the serial line
#   make FG=1 BG=15	colours of the text screen (TMS9918 numbers,
#			jp6502def.i65; default 15 on 4, white on dark blue)
#   make sdcard		boot/sdcard/: the programs to copy onto the SD card
#   make sdimg		boot/sd.img: a card image with them, for the emulator
#   make run		the ROM in the emulator, serial line on this terminal
#   make emu		just build the emulator
#
# The ROM holds the kernel, lib6502, the devices, init, fsdev and the SD
# card filesystem. lsh and the other programs are loaded from the card.

CLOCK=4
SHELLS=
FG=15
BG=4

XA=xa -k -XMASM
FILE=file65
RELOC=reloc65
PYTHON=python3

TRG=boot/geckos.bin

# text is the ROM at $a000; .data at $0300, behind the PCBUF, and .bss
# right behind .data (the second pass below). The zeropage starts at 8,
# 2-7 belong to the kernel.
ROMSTART=40960
DATASTART=768

# what goes onto the card
APPS=../../apps/lsh/lsh ../../apps/lmon/lmon \
	../../apps/file/ls ../../apps/file/mkdir ../../apps/file/rm \
	../../apps/file/rmdir ../../apps/file/mv \
	../../apps/filter/cat ../../apps/filter/more ../../apps/filter/hexdump \
	../../apps/filter/wc \
	../../sysapps/ps ../../sysapps/kill ../../sysapps/lsmem \
	../../sysapps/ontty

# programs for the hardware of this board
JPAPPS=apps/date apps/i2cscan

all: $(TRG)

# assembled every time - it takes a second, and CLOCK and SHELLS
# change it without changing a file
.PHONY: all $(TRG) sdcard sdimg run emu clean

$(TRG):
	$(XA) -R -I../../include -I. -I../.. -DCLOCK_MHZ=$(CLOCK) $(SHELLS) \
		-DVDP_FG=$(FG) -DVDP_BG=$(BG) \
		-bt $(ROMSTART) -bd $(DATASTART) -bz 8 -bb 16384 \
		rom.a65 -o rom.o65 -l rom.lab
	$(FILE) rom.o65
	@# .bss goes right behind .data
	bb=$$(( $(DATASTART) + 0x$$($(FILE) rom.o65 | sed -n 's/.*data segment.*\[\$$\([0-9a-fA-F]*\) bytes\].*/\1/p') )); \
	echo "bss at $$bb"; \
	$(RELOC) -v -bb $$bb -o rom-reloc.o65 rom.o65 > reloc.lst
	$(RELOC) -xt -o rom.text rom-reloc.o65
	@# .data is not in the ROM - the kernel clears the RAM, so every
	@# initial value there has to be zero
	@$(RELOC) -xd -o rom.data rom-reloc.o65 2>/dev/null; \
	if ! cmp -s -n $$(wc -c < rom.data) rom.data /dev/zero; then \
	  echo "error: the ROM code has .data with values other than zero"; exit 1; fi
	@# The kernel ends with the version bytes and the three vectors
	@# (EOK_NOFILL). The gap in front of those twelve bytes is filled,
	@# so that the vectors land at $$fffa. Nothing else moves.
	@len=$$(wc -c < rom.text); free=$$(( 24576 - len )); \
	if [ $$free -lt 0 ]; then echo "ROM too large by $$(( -free )) bytes"; exit 1; fi; \
	echo "ROM: $$len bytes used, $$free free"; \
	mkdir -p boot; \
	( perl -e 'print "\xea" x 8192'; \
	  head -c $$(( len - 12 )) rom.text; \
	  perl -e "print \"\xff\" x $$free"; \
	  tail -c 12 rom.text ) > $@
	@# RAM: .bss has to end below the screen buffers at $$7800
	@end=$$( $(FILE) rom-reloc.o65 | sed -n 's/.*bss  segment @ \$$[0-9a-f]* - \$$\([0-9a-f]*\).*/\1/p' ); \
	echo "RAM: .data/.bss end at \$$$$end, malloc from there to \$$7800"; \
	[ $$(( 0x$$end )) -le $$(( 0x7800 )) ]

$(APPS):
	$(MAKE) -C ../../apps
	$(MAKE) -C ../../sysapps

$(JPAPPS): %: %.a65 devices/i2c_jp.a65 jp6502def.i65
	$(XA) -R -I../../include -I. -I../.. -LLIB6502 -LOSA2KERNEL $< -o $@

sdcard: $(APPS) $(JPAPPS)
	rm -rf boot/sdcard
	mkdir -p boot/sdcard
	cp $(APPS) $(JPAPPS) boot/sdcard/
	@echo "copy the files in boot/sdcard into the root of a FAT32 card"

sdimg: sdcard
	$(PYTHON) emu/fat32img.py create boot/sd.img -s 64 boot/sdcard/*

emu: emu/jp6502emu

emu/jp6502emu: emu/jp6502emu.c
	$(CC) -O2 -Wall -o $@ $<

run: $(TRG) emu
	@[ -f boot/sd.img ] || $(MAKE) sdimg
	emu/jp6502emu -c $(CLOCK) -s boot/sd.img -l rom.lab $(TRG)

clean:
	rm -f $(TRG) rom.lab rom.o65 rom-reloc.o65 rom.text rom.data reloc.lst
	rm -f emu/jp6502emu boot/sd.img $(JPAPPS)
	rm -rf boot/sdcard

