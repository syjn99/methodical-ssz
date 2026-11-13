"""Minimal ELF64 little-endian reader: virtual address -> file bytes. Read-only."""
import struct


class Elf:
    def __init__(self, path):
        self.b = open(path, "rb").read()
        b = self.b
        if b[:4] != b"\x7fELF" or b[4] != 2 or b[5] != 1:
            raise SystemExit(f"{path}: not an ELF64 little-endian file")
        shoff, = struct.unpack_from("<Q", b, 0x28)
        shentsize, shnum = struct.unpack_from("<HH", b, 0x3A)
        self.sections = []
        for i in range(shnum):
            o = shoff + i * shentsize
            _name, typ, _flags, addr, off, size = struct.unpack_from("<IIQQQQ", b, o)
            if addr and typ != 8:  # skip NOBITS (.bss)
                self.sections.append((addr, off, size))

    def read(self, vaddr, n):
        for addr, off, size in self.sections:
            if addr <= vaddr and vaddr + n <= addr + size:
                return self.b[off + vaddr - addr: off + vaddr - addr + n]
        raise KeyError(f"no file bytes for {vaddr:#x}+{n}")

    def section_of(self, vaddr):
        for addr, off, size in self.sections:
            if addr <= vaddr < addr + size:
                return addr, off, size
        raise KeyError(f"{vaddr:#x} not in a section with file bytes")


def read_nm(path):
    """go tool nm -size -sort address: name -> (addr, size)."""
    out = {}
    for line in open(path):
        p = line.split()
        if len(p) >= 4:
            out.setdefault(p[3], (int(p[0], 16), int(p[1])))
    return out


def extent(nm, name):
    """(addr, size) of a symbol; a size-0 group symbol (go:string.*) runs to the next higher address."""
    addr, size = nm[name]
    if size:
        return addr, size
    nxt = min(a for a, _ in nm.values() if a > addr)
    return addr, nxt - addr
