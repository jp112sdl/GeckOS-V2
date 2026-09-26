#!/usr/bin/env python3
"""
fat32img.py - make and inspect FAT32 images for the JP6502 emulator.

  fat32img.py create IMG [-s MB] [-c SECTORS_PER_CLUSTER] [--superfloppy]
                         [--label NAME] [FILE[=PATH] ...]
      A fresh image with an MBR and one FAT32 partition (or none with
      --superfloppy). FILE is copied to PATH on the image, to /BASENAME
      without it. Directories in PATH are created. Names that are not
      plain upper case 8.3 get a long file name entry too, the way PCs
      and Macs write them.

  fat32img.py ls IMG [PATH]         list a directory, long names in []
  fat32img.py cat IMG PATH          file contents to stdout
  fat32img.py check IMG             walk everything, cross-check the FAT
"""

import argparse
import os
import struct
import sys

SEC = 512
EOC = 0x0FFFFFFF


def shortname(name):
    base, dot, ext = name.upper().rpartition(".")
    if not dot:
        base, ext = ext, ""
    keep = lambda s: "".join(ch for ch in s if ch.isalnum() or ch in "!#$%&'()-@^_`{}~")
    base, ext = keep(base), keep(ext)
    if len(base) > 8 or base != name.upper().rpartition(".")[0 if dot else 2]:
        base = base[:6] + "~1"
    return (base[:8].ljust(8) + ext[:3].ljust(3)).encode("latin-1")


def needs_lfn(name):
    base, dot, ext = name.rpartition(".")
    if not dot:
        base, ext = ext, ""
    return (name != name.upper() or len(base) > 8 or len(ext) > 3
            or not base)


def lfn_checksum(sn):
    s = 0
    for b in sn:
        s = (((s & 1) << 7) + (s >> 1) + b) & 0xFF
    return s


class Fat32:
    def __init__(self, path):
        self.f = open(path, "r+b")
        self.part = 0
        bs = self.read(0)
        if not (bs[0] in (0xEB, 0xE9) and struct.unpack_from("<H", bs, 11)[0] == 512):
            for i in range(4):
                e = bs[0x1BE + 16 * i:0x1BE + 16 * i + 16]
                if e[4] in (0x0B, 0x0C):
                    self.part = struct.unpack_from("<I", e, 8)[0]
                    break
            bs = self.read(self.part)
        self.spc = bs[13]
        rsvd = struct.unpack_from("<H", bs, 14)[0]
        self.nfats = bs[16]
        self.fatsz = struct.unpack_from("<I", bs, 36)[0]
        self.root = struct.unpack_from("<I", bs, 44)[0]
        self.totsec = struct.unpack_from("<I", bs, 32)[0]
        self.fsinfo = struct.unpack_from("<H", bs, 48)[0]
        self.fat = self.part + rsvd
        self.data = self.fat + self.nfats * self.fatsz
        self.maxclus = (self.totsec - (self.data - self.part)) // self.spc + 2

    def read(self, lba, n=1):
        self.f.seek(lba * SEC)
        d = self.f.read(n * SEC)
        return d + bytes(n * SEC - len(d))

    def write(self, lba, d):
        self.f.seek(lba * SEC)
        self.f.write(d)

    def fatget(self, c):
        s = self.read(self.fat + c // 128)
        return struct.unpack_from("<I", s, (c % 128) * 4)[0] & 0x0FFFFFFF

    def fatset(self, c, v):
        for k in range(self.nfats):
            lba = self.fat + k * self.fatsz + c // 128
            s = bytearray(self.read(lba))
            old = struct.unpack_from("<I", s, (c % 128) * 4)[0]
            struct.pack_into("<I", s, (c % 128) * 4, (old & 0xF0000000) | v)
            self.write(lba, s)

    def clus_lba(self, c):
        return self.data + (c - 2) * self.spc

    def chain(self, c):
        out = []
        while 2 <= c < self.maxclus:
            out.append(c)
            c = self.fatget(c)
        return out

    def alloc(self, prev=0):
        for c in range(2, self.maxclus):
            if self.fatget(c) == 0:
                self.fatset(c, EOC)
                if prev:
                    self.fatset(prev, c)
                self.write(self.clus_lba(c), bytes(self.spc * SEC))
                return c
        raise RuntimeError("disk full")

    def entries(self, dclus):
        """(name, lfn, attr, clus, size, lba, off)"""
        lfn = []
        for c in self.chain(dclus):
            for s in range(self.spc):
                lba = self.clus_lba(c) + s
                d = self.read(lba)
                for off in range(0, SEC, 32):
                    e = d[off:off + 32]
                    if e[0] == 0:
                        return
                    if e[0] == 0xE5:
                        lfn = []
                        continue
                    if e[11] == 0x0F:
                        part = e[1:11] + e[14:26] + e[28:32]
                        lfn.insert(0, part.decode("utf-16-le", "replace"))
                        continue
                    long = "".join(lfn).split("\x00")[0] if lfn else None
                    lfn = []
                    base = e[0:8].decode("latin-1").rstrip()
                    ext = e[8:11].decode("latin-1").rstrip()
                    name = base + ("." + ext if ext else "")
                    clus = struct.unpack_from("<H", e, 26)[0] | (struct.unpack_from("<H", e, 20)[0] << 16)
                    size = struct.unpack_from("<I", e, 28)[0]
                    yield name, long, e[11], clus, size, lba, off

    def lookup(self, path):
        clus = self.root
        ent = None
        for part in [p for p in path.split("/") if p]:
            for e in self.entries(clus):
                if part.upper() in (e[0].upper(), (e[1] or "").upper()):
                    ent = e
                    clus = e[3] or self.root
                    break
            else:
                return None
        return ent if ent else ("/", None, 0x10, self.root, 0, 0, 0)

    def add_entry(self, dclus, name, attr, clus, size):
        sn = shortname(name)
        ents = []
        if needs_lfn(name):
            u = name.encode("utf-16-le") + b"\x00\x00"
            chunks = [u[i:i + 26] for i in range(0, len(u), 26)]
            chunks[-1] = chunks[-1] + b"\xff" * (26 - len(chunks[-1]))
            ck = lfn_checksum(sn)
            for i in range(len(chunks), 0, -1):
                c = chunks[i - 1]
                e = bytearray(32)
                e[0] = i | (0x40 if i == len(chunks) else 0)
                e[1:11] = c[0:10]
                e[11] = 0x0F
                e[13] = ck
                e[14:26] = c[10:22]
                e[28:32] = c[22:26]
                ents.append(bytes(e))
        e = bytearray(32)
        e[0:11] = sn
        e[11] = attr
        struct.pack_into("<HHHHHHHI", e, 14, 0x6000, 0x5C21, 0x5C21,
                         clus >> 16, 0x6000, 0x5C21, clus & 0xFFFF, size)
        ents.append(bytes(e))
        # find len(ents) consecutive free slots at the end
        last = None
        for c in self.chain(dclus):
            last = c
        slots = []
        for c in self.chain(dclus):
            for s in range(self.spc):
                lba = self.clus_lba(c) + s
                d = self.read(lba)
                for off in range(0, SEC, 32):
                    if d[off] == 0:
                        slots.append((lba, off))
        while len(slots) < len(ents) + 1:
            last = self.alloc(last)
            for s in range(self.spc):
                for off in range(0, SEC, 32):
                    slots.append((self.clus_lba(last) + s, off))
        for (lba, off), e in zip(slots, ents):
            d = bytearray(self.read(lba))
            d[off:off + 32] = e
            self.write(lba, d)

    def mkdir(self, dclus, name):
        c = self.alloc()
        d = bytearray(SEC)
        dot = bytearray(32)
        dot[0:11] = b".          "
        dot[11] = 0x10
        struct.pack_into("<H", dot, 26, c & 0xFFFF)
        struct.pack_into("<H", dot, 20, c >> 16)
        dd = bytearray(32)
        dd[0:11] = b"..         "
        dd[11] = 0x10
        pc = 0 if dclus == self.root else dclus
        struct.pack_into("<H", dd, 26, pc & 0xFFFF)
        struct.pack_into("<H", dd, 20, pc >> 16)
        d[0:32] = dot
        d[32:64] = dd
        self.write(self.clus_lba(c), d)
        self.add_entry(dclus, name, 0x10, c, 0)
        return c

    def put(self, path, data):
        parts = [p for p in path.split("/") if p]
        dclus = self.root
        for p in parts[:-1]:
            e = self.lookup_in(dclus, p)
            dclus = e[3] if e else self.mkdir(dclus, p)
        first = prev = 0
        for i in range(0, len(data), self.spc * SEC):
            c = self.alloc(prev)
            first = first or c
            chunk = data[i:i + self.spc * SEC]
            self.write(self.clus_lba(c), chunk + bytes(self.spc * SEC - len(chunk)))
            prev = c
        self.add_entry(dclus, parts[-1], 0x20, first, len(data))

    def lookup_in(self, dclus, name):
        for e in self.entries(dclus):
            if name.upper() in (e[0].upper(), (e[1] or "").upper()):
                return e
        return None

    def cat(self, ent):
        out = b""
        for c in self.chain(ent[3]):
            out += self.read(self.clus_lba(c), self.spc)
        return out[:ent[4]]


def create(args):
    size = args.size * 1024 * 1024 // SEC
    part = 0 if args.superfloppy else 2048
    spc = args.cluster
    rsvd = 32
    nfats = 2
    tot = size - part
    clus = tot // spc
    fatsz = (clus * 4 + SEC - 1) // SEC + 1
    with open(args.image, "wb") as f:
        f.truncate(size * SEC)
        if part:
            mbr = bytearray(SEC)
            e = struct.pack("<BBBBBBBBII", 0, 0, 0, 0, 0x0C, 0, 0, 0, part, tot)
            mbr[0x1BE:0x1BE + 16] = e
            mbr[510:512] = b"\x55\xaa"
            f.seek(0)
            f.write(mbr)
        bs = bytearray(SEC)
        bs[0:3] = b"\xEB\x58\x90"
        bs[3:11] = b"MSWIN4.1"
        struct.pack_into("<HBHBHHBHHHII", bs, 11, SEC, spc, rsvd, nfats, 0, 0,
                         0xF8, 0, 63, 255, part, tot)
        struct.pack_into("<IHHIHH", bs, 36, fatsz, 0, 0, 2, 1, 6)
        bs[64] = 0x80
        bs[66] = 0x29
        struct.pack_into("<I", bs, 67, 0x1234ABCD)
        bs[71:82] = args.label.upper().encode()[:11].ljust(11)
        bs[82:90] = b"FAT32   "
        bs[510:512] = b"\x55\xaa"
        f.seek(part * SEC)
        f.write(bs)
        fsi = bytearray(SEC)
        struct.pack_into("<I", fsi, 0, 0x41615252)
        struct.pack_into("<I", fsi, 484, 0x61417272)
        struct.pack_into("<II", fsi, 488, 0xFFFFFFFF, 3)
        fsi[510:512] = b"\x55\xaa"
        f.seek((part + 1) * SEC)
        f.write(fsi)
        for k in range(nfats):
            fat = bytearray(SEC)
            struct.pack_into("<III", fat, 0, 0x0FFFFFF8, 0x0FFFFFFF, EOC)
            f.seek((part + rsvd + k * fatsz) * SEC)
            f.write(fat)
    fs = Fat32(args.image)
    for spec in args.files:
        src, _, dst = spec.partition("=")
        fs.put(dst or "/" + os.path.basename(src), open(src, "rb").read())
    # correct free count
    free = sum(1 for c in range(2, fs.maxclus) if fs.fatget(c) == 0)
    d = bytearray(fs.read(fs.part + 1))
    struct.pack_into("<I", d, 488, free)
    fs.write(fs.part + 1, d)


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("create")
    c.add_argument("image")
    c.add_argument("-s", "--size", type=int, default=64)
    c.add_argument("-c", "--cluster", type=int, default=8)
    c.add_argument("--superfloppy", action="store_true")
    c.add_argument("--label", default="GECKOS")
    c.add_argument("files", nargs="*")
    l = sub.add_parser("ls")
    l.add_argument("image")
    l.add_argument("path", nargs="?", default="/")
    k = sub.add_parser("cat")
    k.add_argument("image")
    k.add_argument("path")
    ch = sub.add_parser("check")
    ch.add_argument("image")
    args = ap.parse_args()
    if args.cmd == "create":
        create(args)
    elif args.cmd == "ls":
        fs = Fat32(args.image)
        e = fs.lookup(args.path)
        if not e:
            sys.exit("not found")
        for n, lfn, attr, clus, size, lba, off in fs.entries(e[3] or fs.root):
            if attr & 0x08:
                continue
            kind = "<DIR>" if attr & 0x10 else "%9d" % size
            print("%-12s %9s  clus %-6d %s" % (n, kind, clus, "[%s]" % lfn if lfn else ""))
    elif args.cmd == "cat":
        fs = Fat32(args.image)
        e = fs.lookup(args.path)
        if not e:
            sys.exit("not found")
        sys.stdout.buffer.write(fs.cat(e))
    elif args.cmd == "check":
        fs = Fat32(args.image)
        used = {}
        def walk(dclus, path):
            for n, lfn, attr, clus, size, lba, off in fs.entries(dclus):
                if n in (".", "..") or attr & 0x08:
                    continue
                ch = fs.chain(clus) if clus else []
                for c in ch:
                    if c in used:
                        print("cross-linked", path + n, "and", used[c])
                    used[c] = path + n
                if attr & 0x10:
                    walk(clus, path + n + "/")
                elif len(ch) * fs.spc * SEC < size or (size and not ch):
                    print("short chain", path + n, size, len(ch))
        used.update({c: "/" for c in fs.chain(fs.root)})
        walk(fs.root, "/")
        lost = [c for c in range(2, fs.maxclus) if fs.fatget(c) and c not in used]
        free = sum(1 for c in range(2, fs.maxclus) if fs.fatget(c) == 0)
        fsi = fs.read(fs.part + fs.fsinfo)
        print("clusters in use %d, lost %d, free %d, FSInfo says %d" % (
            len(used), len(lost), free, struct.unpack_from("<I", fsi, 488)[0]))
        if lost:
            print("lost:", lost[:20])
        if fs.fat and fs.nfats > 1:
            for i in range(fs.fatsz):
                if fs.read(fs.fat + i) != fs.read(fs.fat + fs.fatsz + i):
                    print("FAT copies differ in sector", i)
                    break


if __name__ == "__main__":
    main()
