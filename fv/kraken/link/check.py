#!/usr/bin/env python3
"""Link-level check: the converted assembly that Lean reads is the code in the ELF.

Usage: check.py <outdir>      (outdir = fv/kraken/link/out, after build.sh)
       check.py --selftest <outdir>

Inputs in <outdir>: p1bin-amd64 (ELF), target.objdump, p1bin-amd64.nm, norm/*.S.
Writes <outdir>/RESULT. Exit status 1 on any failure.

Checks (REPORT-1b, B1):
 (a) every function: ELF .symtab address and size; objdump instructions cover
     exactly [addr, addr+size) without gaps; objdump bytes = ELF file bytes;
     LLVM (llvm-objdump, an independent decoder) has the same instruction
     boundaries; every label `L_<fn>_<off>` in the .S sits before the
     instruction at fn+off.
 (b) every global label in the .S (call target, `sym+off(%rip)`): the symbol
     exists in the ELF .symtab, its section, and that `addr + len + disp` of the
     original instruction is `sym + off`.
 (c) LabelsFresh in the host program all.S: every label is defined once, so no
     label of a function occurs before it; external labels are not defined in
     all.S (they are the host's other code and data).
 (d) the .S instructions, assembled again by clang --target=x86_64-linux-gnu at
     the original addresses, give the ELF bytes (spelling map for clang only:
     direct `jmpq L` -> `jmp L`). A difference is "encoding" if
     LLVM decodes both byte strings to the same text, "padding" if it is a
     normalized nop, else FAIL.
The bundle hash (sha256 over RESULT up to and including the last PASS line,
which covers the ELF, the .S files, Code.lean and AXIOMS.txt hashes) is the
last line.
"""
import hashlib
import importlib.util
import pathlib
import re
import shutil
import struct
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("conv", HERE / "conv.py")
conv = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conv)


class Fail(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Fail(msg)


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


# ---------------------------------------------------------------- ELF reading
def read_elf(path):
    b = pathlib.Path(path).read_bytes()
    need(b[:6] == b"\x7fELF\x02\x01", "not an ELF64 LSB file")
    shoff, = struct.unpack_from("<Q", b, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", b, 0x3A)
    secs = []
    for i in range(shnum):
        nm, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
            "<IIQQQQIIQQ", b, shoff + i * shentsize)
        secs.append(dict(nm=nm, typ=typ, addr=addr, off=off, size=size, link=link, entsize=entsize))
    strtab = secs[shstrndx]
    for s in secs:
        o = strtab["off"] + s["nm"]
        s["name"] = b[o:b.index(b"\0", o)].decode()
    syms = {}
    for s in secs:
        if s["typ"] != 2:  # SHT_SYMTAB
            continue
        st = secs[s["link"]]
        for j in range(s["size"] // 24):
            nm, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", b, s["off"] + j * 24)
            o = st["off"] + nm
            name = b[o:b.index(b"\0", o)].decode()
            sec = secs[shndx]["name"] if 0 < shndx < len(secs) else str(shndx)
            if name:
                syms.setdefault(name, (value, size, sec))
    return b, secs, syms


def elf_bytes(b, secs, addr, n):
    for s in secs:
        if s["typ"] == 1 and s["addr"] <= addr and addr + n <= s["addr"] + s["size"]:  # PROGBITS
            o = s["off"] + addr - s["addr"]
            return b[o:o + n]
    raise Fail(f"no file bytes at {addr:#x}")


def section_of(secs, addr):
    for s in secs:
        if s["addr"] and s["addr"] <= addr < s["addr"] + s["size"]:
            return s["name"]
    return "?"


# ------------------------------------------------------------ LLVM decoding
def tool(name):
    p = shutil.which(name)
    if p:
        return p
    return subprocess.check_output(["xcrun", "--find", name], text=True).strip()


def llvm_decode(elf, lo, hi):
    text = subprocess.check_output(
        [tool("llvm-objdump"), "-d", f"--start-address={lo}", f"--stop-address={hi}", str(elf)], text=True)
    out = {}
    for line in text.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)$", line)
        if m:
            out[int(m[1], 16)] = (bytes.fromhex(m[2]), re.sub(r"\s+", " ", m[3]).split(" <")[0].strip())
    return out


# ---------------------------------------------------------------- the check
def parse_S(path):
    """Directives of a converted .S: ('label', name) or ('ins', text)."""
    out = []
    for line in pathlib.Path(path).read_text().splitlines():
        if not line.strip():
            continue
        if line.startswith("  "):
            out.append(("ins", line.strip()))
        else:
            need(line.endswith(":"), f"{path}: bad line {line!r}")
            out.append(("label", line[:-1]))
    return out


def run(outdir, log):
    outdir = pathlib.Path(outdir)
    elf = outdir / "p1bin-amd64"
    b, secs, esyms = read_elf(elf)
    conv.CLEANED.clear()
    fns = conv.read_objdump(outdir / "target.objdump")
    nm = conv.read_nm(outdir / "p1bin-amd64.nm")
    # Go's nm adds size-0 group symbols (`type:*`, `go:string.*`) that are not in
    # the ELF .symtab; they are taken from nm with the section of their address.
    nmonly = set()
    for a, sz, name in nm:
        if name not in esyms:
            esyms[name] = (a, sz, section_of(secs, a))
            nmonly.add(name)
    # Sanitized name -> original names over the whole binary: a referenced name
    # must have exactly one original (stricter than conv.py, which sees only used names).
    rev = {}
    for name in esyms:
        o = name.replace(conv.MOD + "fv/kraken/", "").replace(conv.MOD, "")
        o = re.sub(r"[^A-Za-z0-9_.]", "_", re.sub(r"\(\*(\w+)\)", r"\1", o))
        rev.setdefault(o, set()).add(name)

    def orig(g):
        need(len(rev.get(g, ())) == 1, f"name {g} has originals {sorted(rev.get(g, ()))}")
        return next(iter(rev[g]))
    raw = {}
    for line in (outdir / "target.objdump").read_text().splitlines():
        m = re.match(r"\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+", line)
        if m:
            raw[int(m[1], 16)] = bytes.fromhex(m[2])
    clean2orig = {}
    hostlabels = []  # all.S labels in order
    externals = {}   # clean name -> (addr, section, kind)
    per_fn = []
    for f in fns:
        name = conv.clean(f["name"])
        clean2orig[name] = f["name"]
        ins = f["ins"]
        lo, hi = ins[0][0], ins[-1][0] + ins[-1][1]
        # (a) symbol extent
        need(f["name"] in esyms, f"{f['name']}: not in ELF .symtab")
        sa, ss, ssec = esyms[f["name"]]
        need((sa, ss) == (lo, hi - lo), f"{name}: symtab {sa:#x}+{ss} vs objdump {lo:#x}+{hi - lo}")
        need(ssec == ".text", f"{name}: section {ssec}")
        dec = llvm_decode(elf, lo, hi)
        need(set(dec) == {a for a, _, _ in ins}, f"{name}: LLVM instruction boundaries differ")
        for a, n, _ in ins:
            need(raw[a] == elf_bytes(b, secs, a, n) == dec[a][0], f"{name}: bytes differ at {a:#x}")
        # (a) labels of the .S against instruction addresses
        S = parse_S(outdir / "norm" / f"{name}.S")
        need(S[0] == ("label", name), f"{name}: first directive is not the function label")
        k = 0
        for d in S[1:]:
            if d[0] == "label":
                m = re.fullmatch(re.escape(f"L_{name}_") + r"([0-9a-f]+)", d[1])
                need(m, f"{name}: unexpected local label {d[1]}")
                need(k < len(ins) and ins[k][0] == lo + int(m[1], 16),
                     f"{name}: label {d[1]} not before the instruction at its address")
            else:
                k += 1
        need(k == len(ins), f"{name}: .S has {k} instructions, objdump {len(ins)}")
        hostlabels += [d[1] for d in S if d[0] == "label"]
        # (b) global references
        sins = [d[1] for d in S if d[0] == "ins"]
        for (a, n, att), st in zip(ins, sins):
            br = conv.BRANCH.match(att)
            if br and not (lo <= int(br[2], 16) < hi):
                t = int(br[2], 16)
                g = st.split()[-1]
                o = orig(g)
                need(esyms[o][0] == t, f"{name}: call/jump target {g} != {t:#x}")
                externals.setdefault(g, (t, esyms[o][2], "code"))
            r = conv.RIP.search(att)
            if r:
                t = a + n + int(r[1], 0)
                m = re.search(r"([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)", st)
                need(m, f"{name}: rip operand not converted: {st}")
                g, off = m[1], int(m[2] or 0)
                o = orig(g)
                sa, ss, ssec = esyms[o]
                need(sa + off == t, f"{name}: {g}+{off} = {sa + off:#x}, instruction refers to {t:#x}")
                kind = "in-symbol" if off < max(ss, 1) else "group(nearest preceding symbol)"
                if o in nmonly:
                    kind += ", nm-only symbol"
                externals.setdefault(g if not off else f"{g}+{off}", (t, ssec, kind))
        per_fn.append((name, lo, hi, ins, sins))
        log(f"PASS (a) {name}: {len(ins)} instructions, {hi - lo} bytes, symtab/objdump/LLVM/ELF bytes and labels agree")
    # (b) report
    for g, (t, sec, kind) in sorted(externals.items(), key=lambda x: x[1][0]):
        log(f"PASS (b) {g} = {t:#x} {sec} {kind}")
    # (c) label uniqueness in the host program all.S
    allS = parse_S(outdir / "norm" / "all.S")
    labs = [d[1] for d in allS if d[0] == "label"]
    need(labs == hostlabels, "all.S labels are not the concatenation of the functions' labels")
    dup = {l for l in labs if labs.count(l) > 1}
    need(not dup, f"duplicate labels in all.S: {sorted(dup)}")
    fnames = {x[0] for x in per_fn}
    clash = ({g.split("+")[0] for g in externals} & set(labs)) - fnames
    need(not clash, f"external labels defined in all.S: {sorted(clash)}")
    internal = sorted({g for g in externals} & fnames)
    for g in internal:
        need(externals[g][0] == next(lo for n, lo, *_ in per_fn if n == g), f"call to {g} not at its entry")
    log(f"PASS (c) all.S: {len(labs)} labels, each defined once; {len(externals) - len(internal)} external "
        f"references not defined in all.S; {len(internal)} calls to target functions at their entry: {internal}")
    # (d) reassembly
    diffs = reassemble(per_fn, {g.split("+")[0]: orig(g.split("+")[0]) for g in externals}, esyms, b, secs, outdir)
    for name, a, kind, orig, new, txt in diffs:
        log(f"DIFF (d) {name} {a:#x} {kind}: elf {orig.hex()} asm {new.hex()} {txt}")
    need(all(k != "FAIL" for _, _, k, _, _, _ in diffs), "reassembly mismatch (see DIFF FAIL lines)")
    n_ins = sum(len(x[3]) for x in per_fn)
    log(f"PASS (d) {n_ins} instructions reassembled by clang x86_64-linux-gnu: "
        f"{n_ins - len(diffs)} byte-identical, {sum(d[2] == 'encoding' for d in diffs)} encoding, "
        f"{sum(d[2] == 'padding' for d in diffs)} padding")
    return per_fn


def reassemble(per_fn, externals, esyms, b, secs, outdir):
    """One section, every function and external symbol at its ELF address via .org."""
    anchors = []
    for name, lo, hi, ins, sins in per_fn:
        anchors.append((lo, name, ins, sins))
    fnames = {x[0] for x in per_fn}
    for g in externals:
        if g not in fnames:
            anchors.append((esyms[externals[g]][0], g, None, None))
    anchors.sort(key=lambda x: (x[0], x[2] is not None))
    base = anchors[0][0]
    lines = [".text", ".att_syntax", ".code64"]
    for a, name, ins, sins in anchors:
        lines.append(f".org {a - base:#x}")
        if ins is None:
            lines.append(f"{name}:")
            continue
        lines.append(f"{name}:")
        for (ia, n, att), st in zip(ins, sins):
            lines.append(f".org {ia - base:#x}")
            off = ia - a
            lab = f"L_{name}_{off:x}"
            lines.append(f"{lab}:")
            # spelling only: LLVM's assembler takes `jmp L`, not `jmpq L`, for a direct jump
            lines.append("  " + re.sub(r"^jmpq (?=[A-Za-z_])", "jmp ", st))
    with tempfile.TemporaryDirectory() as d:
        src = pathlib.Path(d) / "re.S"
        obj = pathlib.Path(d) / "re.o"
        src.write_text("\n".join(lines) + "\n")
        r = subprocess.run([tool("clang"), "--target=x86_64-linux-gnu", "-c", "-x", "assembler", str(src),
                            "-o", str(obj)], capture_output=True, text=True)
        need(r.returncode == 0, "clang: " + r.stderr[:2000])
        ob, osecs, _ = read_elf(obj)
        rel = [s for s in osecs if s["name"] == ".rela.text"]
        need(not rel or rel[0]["size"] == 0, "reassembly left relocations in .text")
        text = next(s for s in osecs if s["name"] == ".text")
        body = ob[text["off"]:text["off"] + text["size"]]
    diffs = []
    for name, lo, hi, ins, sins in per_fn:
        for (a, n, att), st in zip(ins, sins):
            orig = elf_bytes(b, secs, a, n)
            new = body[a - base:a - base + n]
            if orig == new:
                continue
            if att in conv.NORM:
                diffs.append((name, a, "padding", orig, new.rstrip(b"\0"), f"{att} -> nop"))
                continue
            t1, t2 = decode_bytes(orig, a, outdir), decode_bytes(new, a, outdir)
            diffs.append((name, a, "encoding" if t1 == t2 and t1 else "FAIL", orig, new, f"{att} | {t1} | {t2}"))
    return diffs


def decode_bytes(bs, addr, outdir):
    """LLVM text of the first instruction of bs, decoded as x86-64 at addr."""
    with tempfile.TemporaryDirectory() as d:
        s = pathlib.Path(d) / "d.S"
        o = pathlib.Path(d) / "d.o"
        s.write_text(".text\n.byte " + ",".join(str(x) for x in bs) + "\n")
        subprocess.run([tool("clang"), "--target=x86_64-linux-gnu", "-c", "-x", "assembler", str(s), "-o", str(o)],
                       check=True, capture_output=True)
        text = subprocess.check_output([tool("llvm-objdump"), "-d", f"--adjust-vma={addr}", str(o)], text=True)
    for line in text.splitlines():
        m = re.match(r"\s*[0-9a-f]+:\s+((?:[0-9a-f]{2} )+)\s*(.*)$", line)
        if m:
            return (len(bytes.fromhex(m[1])), re.sub(r"\s+", " ", m[2]).split(" <")[0].strip())
    return None


def main(outdir):
    outdir = pathlib.Path(outdir)
    lines = []

    def log(s):
        print(s)
        lines.append(s)

    try:
        run(outdir, log)
    except (Fail, SystemExit) as e:
        log(f"FAIL {e}")
        (outdir / "RESULT").write_text("\n".join(lines) + "\n")
        return 1
    lean = HERE.parent / "lean"
    log(f"elf sha256 {sha(outdir / 'p1bin-amd64')}")
    for p in sorted((outdir / "norm").glob("*.S")):
        log(f"S sha256 {sha(p)} {p.name}")
    for p in [lean / "Fk" / "Code.lean", HERE.parent / "AXIOMS.txt"]:
        if p.exists():
            log(f"file sha256 {sha(p)} {p.relative_to(HERE.parent)}")
    log("PASS all")
    body = "\n".join(lines) + "\n"
    body += f"BUNDLE sha256 {hashlib.sha256(body.encode()).hexdigest()}\n"
    (outdir / "RESULT").write_text(body)
    print(body.splitlines()[-1])
    return 0


def selftest(outdir):
    """Sensitivity (C22): mutated inputs must fail; a pure relabeling must pass."""
    outdir = pathlib.Path(outdir)
    cases = []
    with tempfile.TemporaryDirectory() as d:
        def copy():
            t = pathlib.Path(tempfile.mkdtemp(dir=d))
            shutil.copytree(outdir, t, dirs_exist_ok=True)
            return t
        # 1. drop one instruction from a .S
        t = copy(); p = t / "norm" / "target.Scalars.UnmarshalSSZ.S"
        ls = p.read_text().splitlines(); del ls[5]; p.write_text("\n".join(ls) + "\n")
        cases.append(("drop an instruction", t, False))
        # 2. change an immediate
        t = copy(); p = t / "norm" / "target.Scalars.UnmarshalSSZ.S"
        p.write_text(p.read_text().replace("cmp $0x10,%rcx", "cmp $0x11,%rcx"))
        cases.append(("change an immediate", t, False))
        # 3. move a label one instruction later
        t = copy(); p = t / "norm" / "target.Scalars.UnmarshalSSZ.S"
        ls = p.read_text().splitlines()
        i = next(j for j, l in enumerate(ls) if l.startswith("L_") and j > 2)
        ls[i], ls[i + 1] = ls[i + 1], ls[i]; p.write_text("\n".join(ls) + "\n")
        cases.append(("move a label", t, False))
        # 4. objdump line without // (converter must fail)
        t = copy(); p = t / "target.objdump"
        s = p.read_text(); p.write_text(s.replace("// mov $0x10,%eax", "", 1))
        cases.append(("objdump line without //", t, False))
        # 5. global reference to the wrong symbol
        t = copy(); p = t / "norm" / "target.Scalars.UnmarshalSSZ.S"
        p.write_text(p.read_text().replace("ssz.ErrSize+8(%rip)", "ssz.ErrSize(%rip)", 1))
        cases.append(("wrong global offset", t, False))
        # 6. unchanged copy passes
        t = copy()
        cases.append(("unchanged copy", t, True))
        ok = True
        for name, t, expect in cases:
            why = ""
            try:
                conv.CLEANED.clear()
                run(t, lambda s: None)
                got = True
            except (Fail, SystemExit) as e:
                got, why = False, str(e).splitlines()[0][:120]
            print(f"selftest {name}: {'pass' if got else 'fail'} (expected {'pass' if expect else 'fail'}) {why}")
            ok &= got == expect
    return 0 if ok else 1


if __name__ == "__main__":
    if sys.argv[1] == "--selftest":
        sys.exit(selftest(sys.argv[2]))
    sys.exit(main(sys.argv[1]))
