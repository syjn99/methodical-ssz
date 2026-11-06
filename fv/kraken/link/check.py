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
     normalized nop, else FAIL. At a padding position the .S instruction must
     be `nop`, its new byte must be 0x90, and LLVM must decode the original
     bytes as a nop (1b-fix X6: a `retq` there used to pass).
 (e) all.S has the same directives as the per-function .S files, in order
     (instructions included, not only labels).
 (f) lean/Fk/SHash.lean is byte for byte the text that link/shash.sh writes
     for the sha256 of every .S file that Lean reads (link/out/norm/*.S,
     lean/Fk/*.S). No comment or expression is interpreted, so a suffix such
     as `|>.take 0` or a comment inside a hash string fails; a stale SHash
     means Lake may not rebuild the proofs.
 (g) format strings that the proofs fix. Lean text is read with comments
     removed by a scanner that knows string literals. A definition in FMTS is
     the only one of its name and is exactly `def n : List UInt8 := [..]` up
     to the next command. For every `<name>.At (label "go_string._" + off)`
     (any whitespace) the ELF bytes at `go_string._+off` equal the Lean byte
     list, and the Go source has a `fmt.Errorf` call (go/parser, golits.go)
     whose literal has the same bytes; strings fixed by length only (FMTLEN)
     are a whole Go literal in the ELF. Every `go_string._` reference in every
     Fk/*.lean is classified by declaration role (theorem over every Host or
     witness on one concrete host); a reference that is not a checked
     placement, a checked pointer, or witness fill/label fails.
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


# (g): format strings fixed by the reject proofs: (Lean file that defines the
# byte list, Lean name, Go source file relative to the repository root). The
# ELF offset is read from every `<name>.At (label "go_string._" + off)` in the
# Lean sources, so a proof that names a stale offset fails here.
# The last field says whether the proofs use the string with FmtErrorfNilC
# (no arguments), which needs the format to have no `%`.
FMTS = [("LcReject.lean", "lcFmtZero", "fv/kraken/target/types1b.ssz.go", True),
        ("LcReject.lean", "lcFmtShort", "fv/kraken/target/types1b.ssz.go", True),
        ("Vbv.lean", "vbvFmt", "ssz/unmarshal.go", True),
        ("BvSpec.lean", "bvFmtJ", "fv/kraken/target/types1b.ssz.go", False),
        ("BlMarshal.lean", "blFmtB", "fv/kraken/target/types1b.ssz.go", False)]
# (g): format strings that a statement places by length only (any bytes `fs`
# with `fs.length = n`): (Lean file, go_string._ offset, n, Go source file).
# The ELF bytes there must be a whole fmt.Errorf literal of the Go source.
FMTLEN = [("LuRejectCall.lean", 40290, 56, "fv/kraken/target/types.ssz.go"),
          ("LuRejectCall.lean", 42646, 68, "fv/kraken/target/types.ssz.go")]


def strip_lean_comments(txt):
    """Lean text with `--` line comments and nested `/- -/` block comments
    replaced by spaces (newlines kept). A scanner with string state: inside a
    string literal `"..."` (with `\\` escapes) or a char literal, `/-` and `--`
    are text (astra reprove-fix finding 1)."""
    out, i, n = [], 0, len(txt)
    while i < n:
        c = txt[i]
        if c == '"':
            j = i + 1
            while j < n and txt[j] != '"':
                j += 2 if txt[j] == "\\" else 1
            need(j < n, "(lean) unterminated string literal")
            out.append(txt[i:j + 1]); i = j + 1
        elif c == "'" and (i == 0 or not (txt[i - 1].isalnum() or txt[i - 1] in "_'.!?")):
            m = re.match(r"'(\\.[^']*|[^'\\])'", txt[i:])
            k = m.end() if m else 1
            out.append(txt[i:i + k]); i += k
        elif txt.startswith("--", i):
            j = txt.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j
        elif txt.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if txt.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif txt.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            need(not depth, "(lean) unterminated block comment")
            out.append(re.sub(r"[^\n]", " ", txt[i:j])); i = j
        else:
            out.append(c); i += 1
    return "".join(out)


def shash_text(files):
    """The exact text that link/shash.sh writes for these files (same order)."""
    return ("module\n"
            "/-! Generated by link/shash.sh: sha256 of link/out/norm/*.S (Lake rebuild trigger). -/\n"
            "@[expose] public def Fk.sHash : List String := [\n"
            + "".join(f'  "{sha(f)} {f.name}",\n' for f in files) + '  "end"]\n')


GS_REF = re.compile(r'(?:(?P<z>\(z (?P<n>\d+)\))|(?P<name>[A-Za-z_][A-Za-z0-9_]*))\.At\s*\(\s*label\s+"go_string\._"\s*\+\s*(?P<off>\d+)\s*\)'
                    r'|label\s+"go_string\._"\s*\+\s*(?P<poff>\d+)\s*\)'
                    r'|(?P<lab>\.label\s+"go_string\._"|\btheorem\s+label_gs\s*:\s*label\s+"go_string\._"\s*=)')
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|public|noncomputable)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|example)\b\s*([^\s:(\[{]*)", re.M)


def lean_gs_refs(src):
    """Every go_string._ reference in comment-free Lean sources, with its kind
    (place, fill, ptr, label), format name, offset, enclosing declaration and
    role. A module is a witness module if it builds a concrete host
    (`instance host : Host := mkHost`); a declaration there is a witness unless
    it takes `[Host]` (then it is a theorem over every host)."""
    out = []
    for fname, txt in src.items():
        wmod = re.search(r"^instance host : Host := mkHost", txt, re.M) and not re.search(r"^variable \[Host\]", txt, re.M)
        decls = [(m.start(), m[2] or m[1]) for m in DECL.finditer(txt)]
        covered = set()
        for m in GS_REF.finditer(txt):
            covered |= set(range(m.start(), m.end()))
            d = [x for x in decls if x[0] <= m.start()]
            dstart, dname = d[-1] if d else (0, "-")
            head = txt[dstart:txt.find(":=", dstart) if ":=" in txt[dstart:] else len(txt)]
            role = "witness" if wmod and "[Host]" not in head else "theorem"
            kind = "label" if m["lab"] else "fill" if m["z"] else "place" if m["name"] else "ptr"
            if kind == "ptr" and re.search(r"\.At\s*\(\s*$", txt[max(0, m.start() - 40):m.start()]):
                kind = "place-unknown"  # bytes of an unparsed expression placed at go_string._+off
            off = int(m["off"] or m["poff"]) if (m["off"] or m["poff"]) else None
            out.append(dict(file=fname, line=txt.count("\n", 0, m.start()) + 1, decl=dname, role=role,
                            kind=kind, name=m["name"], off=off))
        for m in re.finditer(r"go_string", txt):
            if m.start() not in covered:
                out.append(dict(file=fname, line=txt.count("\n", 0, m.start()) + 1, decl="?", role="?",
                                kind="unparsed", name=None, off=None))
    return out


def lean_bytes(src, lfile, ldef):
    """The byte list of `def <ldef> : List UInt8 := [..]`: the only definition
    of that name in Fk/*.lean, in lfile, the whole (comment-free) line, and the
    next non-blank line starts a new command (no suffix such as `|>.map f`)."""
    defs = [(f, m) for f, t in src.items() for m in re.finditer(r"\bdef\s+" + re.escape(ldef) + r"\b", t)]
    need(len(defs) == 1 and defs[0][0] == lfile, f"(g) {ldef}: {len(defs)} definitions, want one in {lfile}")
    txt = src[lfile]
    ls = txt[defs[0][1].start():].split("\n")
    k = 1 + next((i for i, l in enumerate(ls[1:]) if l.strip() and not l[0].isspace()), len(ls) - 1)
    m = re.fullmatch(r"def " + re.escape(ldef) + r" : List UInt8 :=\s*\[(\d+(?:,\s*\d+)*)\]\s*", "\n".join(ls[:k]))
    need(m, f"(g) {ldef}: the definition is not exactly `def {ldef} : List UInt8 := [n, ...]` up to the next command")
    nxt = ls[k] if k < len(ls) else ""
    need(re.match(r"(theorem|lemma|def|abbrev|instance|example|end|namespace|section|open|set_option|@\[|"
                  r"private|protected|public|noncomputable|variable|/--|#)\b", nxt) or nxt.startswith(("@[", "/--")),
         f"(g) {ldef}: the line after the definition does not start a new command: {nxt!r}")
    return bytes(int(x) for x in m[1].split(","))


def go_literals(root, files):
    """{file: [(line, value)]}: first string argument of every fmt.Errorf call
    (go/parser, link/golits.go)."""
    env = dict(__import__("os").environ)
    env["GOROOT"] = subprocess.check_output(["go", "env", "GOROOT"], text=True).strip()
    js = subprocess.check_output(["go", "run", str(HERE / "golits.go"), "--"] + [str(root / f) for f in files],
                                 text=True, env=env)
    got = __import__("json").loads(js)
    return {f: [(x["line"], x["value"]) for x in got[str(root / f)]] for f in files}


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


def run(outdir, log, shash=True, shash_file=None, lean=None, fmts=None, goroot=None):
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
    # (e) all.S directives = per-function directives
    want = []
    for name, *_ in per_fn:
        want += parse_S(outdir / "norm" / f"{name}.S")
    need(allS == want, "all.S directives differ from the per-function .S files" +
         next((f" (first at directive {i}: {x} vs {y})" for i, (x, y) in enumerate(zip(allS, want)) if x != y),
              f" (lengths {len(allS)} vs {len(want)})"))
    log(f"PASS (e) all.S: {len(allS)} directives equal the {len(per_fn)} function files in order")
    # (f) SHash.lean is current. The file must be byte for byte what shash.sh
    # writes (fixed grammar, no comment or expression to interpret): a suffix,
    # a comment inside a string or a stale hash all fail (astra reprove-fix 1).
    lean = pathlib.Path(lean or HERE.parent / "lean")
    files = sorted((outdir / "norm").glob("*.S")) + sorted((lean / "Fk").glob("*.S"))
    shtxt = pathlib.Path(shash_file or lean / "Fk" / "SHash.lean").read_text()
    if not shash:
        log("SKIP (f) (selftest copy)")
    else:
        exp = shash_text(files)
        need(shtxt == exp, "(f) lean/Fk/SHash.lean is not the text link/shash.sh writes; run link/shash.sh" +
             next((f" (first difference at line {i + 1}: {x!r} vs {y!r})"
                   for i, (x, y) in enumerate(zip(shtxt.splitlines(), exp.splitlines())) if x != y),
                  f" ({len(shtxt.splitlines())} vs {len(exp.splitlines())} lines)"))
        log(f"PASS (f) lean/Fk/SHash.lean is the exact shash.sh text for all {len(files)} .S files")
    # (g) format strings: ELF rodata = Go source literal = Lean byte list.
    g = "go_string._"
    gsa = esyms[orig(g)][0]
    src = {q.name: strip_lean_comments(q.read_text()) for q in sorted((lean / "Fk").glob("*.lean"))}
    root = pathlib.Path(goroot or HERE.parent.parent.parent)
    fmts = FMTS if fmts is None else fmts
    lits = go_literals(root, sorted({x[2] for x in fmts} | {x[3] for x in FMTLEN}))
    refs = lean_gs_refs(src)
    names = {x[1] for x in fmts}
    lenplaces = {(x[0], x[1]) for x in FMTLEN}
    checked = set()
    for lfile, ldef, gofile, nopct in fmts:
        lb = lean_bytes(src, lfile, ldef)
        lines = [l for l, v in lits[gofile] if v.encode() == lb]
        need(lines, f"(g) {gofile} has no fmt.Errorf literal (go/parser) equal to Lean {ldef}")
        need(not nopct or b"%" not in lb, f"(g) {ldef} has a %")
        offs = sorted({r["off"] for r in refs if r["name"] == ldef})
        need(offs, f"(g) no Lean statement places {ldef} at go_string._+off")
        for off in offs:
            eb = elf_bytes(b, secs, gsa + off, len(lb))
            need(lb == eb, f"(g) {ldef}: Lean {lb!r} ELF {g}+{off} {eb!r}")
            log(f"PASS (g) {g}+{off} ({len(lb)} bytes) = Lean {ldef} = {gofile} lines {lines}")
        checked |= set(offs)
    for lfile, off, n, gofile in FMTLEN:
        need(any(r["file"] == lfile and r["off"] == off and r["name"] == "fs" for r in refs),
             f"(g) {lfile} does not place a string at {g}+{off}")
        eb = elf_bytes(b, secs, gsa + off, n)
        lines = [l for l, v in lits[gofile] if v.encode() == eb]
        need(lines, f"(g) ELF {g}+{off} ({n} bytes) {eb!r} is not a fmt.Errorf literal (go/parser) of {gofile}")
        checked.add(off)
        log(f"PASS (g) {g}+{off} ({n} bytes, length only in {lfile}) = {gofile} lines {lines}")
    # Inventory by declaration role (astra reprove-fix finding 2), over every
    # Fk/*.lean: a theorem (a declaration over every Host) may name go_string._
    # only at a checked offset, with a checked format name or as a pointer
    # value; a witness (a declaration about one concrete host) may also place
    # zero fill bytes `(z n)` there and name the label itself. Any other form,
    # and any go_string._ text the parser does not read, fails.
    bad = []
    for r in refs:
        k, role, off = r["kind"], r["role"], r["off"]
        ok = (k == "place" and (r["name"] in names or (r["file"], off) in lenplaces and r["name"] == "fs")
              or k == "ptr" and off in checked
              or k == "fill" and role == "witness"
              or k == "label" and role == "witness")
        if not ok:
            bad.append(f'{r["file"]}:{r["line"]} {r["decl"]} ({role}) {k} {r["name"] or ""} {off if off is not None else ""}'.strip())
    need(not bad, f"(g) go_string._ references not checked: {bad}")
    log(f"PASS (g) inventory: {len(refs)} go_string._ references in {len({r['file'] for r in refs})} files, "
        f"checked offsets {sorted(checked)}; witness fill and label references: "
        f"{sum(r['kind'] in ('fill', 'label') for r in refs)}")
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
                t0 = decode_bytes(orig, a, outdir)
                okpad = (st == "nop" and new[:1] == b"\x90" and not any(new[1:])
                         and t0 is not None and t0[0] == n
                         and re.match(r"^(data16 )*(nop[lwq]?|xchg %ax, ?%ax)( |$)", t0[1]))
                diffs.append((name, a, "padding" if okpad else "FAIL", orig, new.rstrip(b"\0"),
                              f"{att} -> {st} | {t0}"))
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
        # 6. a padding nop becomes retq in the function file and in all.S (1b-fix X6)
        t = copy(); p = t / "norm" / "target.BitVec.UnmarshalSSZ.S"
        ls = p.read_text().split("\n"); assert ls[8] == "  nop"; ls[8] = "  retq"; p.write_text("\n".join(ls))
        p = t / "norm" / "all.S"
        ls = p.read_text().split("\n"); i = ls.index("target.BitVec.UnmarshalSSZ:") + 8
        assert ls[i] == "  nop"; ls[i] = "  retq"; p.write_text("\n".join(ls))
        cases.append(("padding nop -> retq", t, False))
        # 7. all.S instruction differs from the function file (labels unchanged)
        t = copy(); p = t / "norm" / "all.S"
        p.write_text(p.read_text().replace("cmp $0x10,%rcx", "cmp $0x11,%rcx", 1))
        cases.append(("all.S instruction changed", t, False))
        # 8. a .S changes (one blank line, same directives) but SHash.lean is not regenerated
        t = copy(); p = t / "norm" / "target.Scalars.SizeSSZ.S"
        p.write_text(p.read_text() + "\n")
        cases.append(("stale SHash.lean", t, False))
        # 9. hashes only in a comment, Fk.sHash itself empty (astra 1b-fix finding 2)
        t = copy(); sh = t / "SHash.lean"
        body = (HERE.parent / "lean" / "Fk" / "SHash.lean").read_text()
        sh.write_text("module\n/-\n" + body.replace("module\n", "", 1) + "\n-/\n"
                      "@[expose] public def Fk.sHash : List String := [\"end\"]\n")
        cases.append(("hashes only in a comment", t, False))
        # Lean-side mutations run on a copy of lean/Fk (astra reprove 1, 2).
        def leancopy(t):
            shutil.copytree(HERE.parent / "lean" / "Fk", t / "lean" / "Fk")
            return t / "lean" / "Fk"
        # 10. a suffix after the list literal: the value of Fk.sHash is [] (astra reprove 1)
        t = copy(); fk = leancopy(t); sh = fk / "SHash.lean"
        sh.write_text(sh.read_text().rstrip("\n") + " |>.take 0\n")
        cases.append(("SHash suffix .take 0", t, False))
        # 11. blFmtB value: first byte 66 -> 67 ("B: %w" -> "C: %w") (astra reprove 2)
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace("def blFmtB : List UInt8 := [66,", "def blFmtB : List UInt8 := [67,"))
        cases.append(("blFmtB value 66 -> 67", t, False))
        # 12. blFmtB offset: every statement places it one byte later
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace('blFmtB.At (label "go_string._" + 526)', 'blFmtB.At (label "go_string._" + 527)'))
        cases.append(("blFmtB offset 526 -> 527", t, False))
        # 13. blFmtB not registered in FMTS: the inventory finds go_string._+526
        t = copy()
        cases.append(("blFmtB not registered", t, False))
        # astra reprove-fix mutations (review/review-reprove-fix-mut-*-astra.log).
        # 15. a balanced comment inside the first hash string (finding 1)
        t = copy(); fk = leancopy(t); sh = fk / "SHash.lean"
        tx = sh.read_text(); i = tx.index('  "') + 3 + 8
        sh.write_text(tx[:i] + "/-x-/" + tx[i:])
        cases.append(("SHash comment inside a string", t, False))
        # 16. blFmtB value with a suffix on the same line (finding 2, fmt-value-suffix)
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace("def blFmtB : List UInt8 := [66, 58, 32, 37, 119]",
                                           "def blFmtB : List UInt8 := [66, 58, 32, 37, 119].map (fun b => b + 1)"))
        cases.append(("blFmtB suffix .map", t, False))
        # 17. the same suffix on the next line at column 0
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace("def blFmtB : List UInt8 := [66, 58, 32, 37, 119]\n",
                                           "def blFmtB : List UInt8 := [66, 58, 32, 37, 119]\n|>.map (fun b => b + 1)\n"))
        cases.append(("blFmtB suffix on the next line", t, False))
        # 18. one placement written with two spaces and offset 527 (second-offset-space)
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace('blFmtB.At (label "go_string._" + 526)', 'blFmtB.At (label  "go_string._" + 527)', 1))
        cases.append(("blFmtB offset with two spaces", t, False))
        # 19. Go literal changed, the old call kept in a comment (fmtlen-go-comment)
        t = copy(); gr = t / "gosrc"
        for f in ("fv/kraken/target/types.ssz.go", "fv/kraken/target/types1b.ssz.go", "ssz/unmarshal.go"):
            (gr / f).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(HERE.parent.parent.parent / f, gr / f)
        f = gr / "fv/kraken/target/types.ssz.go"; tx = f.read_text()
        a = 'fmt.Errorf("ssz-max exceeded: c.L has %d elements, ssz-max is 16: %w", numElem, ssz.ErrListTooBig)'
        assert a in tx
        f.write_text(tx.replace(a, "// " + a + "\n\t\t\treturn " + a.replace("exceeded:", "exceeded;"), 1))
        cases.append(("Go literal only in a comment", t, False))
        # 20. a declaration over every Host in a Wit file places fill bytes at a new offset (wit-exclusion)
        t = copy(); fk = leancopy(t); f = fk / "WitBlR.lean"
        f.write_text(f.read_text().replace("end Fk.WitBlR", "theorem astra_gen [Host] : Eq ((z 5).At (label \"go_string._\" + 99999).toBitVec)\n"
                                           "    = Eq ((z 5).At (label \"go_string._\" + 99999).toBitVec) := rfl\n\nend Fk.WitBlR"))
        cases.append(("Wit file, theorem over every Host", t, False))
        # 21. a witness names an unknown byte list at a new offset
        t = copy(); fk = leancopy(t); f = fk / "WitBlR.lean"
        f.write_text(f.read_text().replace("end Fk.WitBlR", "def junk : DataMem → Prop := Eq ((z 1 ++ z 1).At (label \"go_string._\" + 99999).toBitVec)\n\nend Fk.WitBlR"))
        cases.append(("Wit file, unknown placement", t, False))
        # 22. a theorem places an unparsed byte expression at a checked offset
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace('Eq (blFmtB.At (label "go_string._" + 526)', 'Eq ((blFmtB ++ []).At (label "go_string._" + 526)', 1))
        cases.append(("unparsed bytes at a checked offset", t, False))
        # 23. an offset written as a sum (not read by the parser)
        t = copy(); fk = leancopy(t); f = fk / "BlMarshal.lean"
        f.write_text(f.read_text().replace('blFmtB.At (label "go_string._" + 526)', 'blFmtB.At (label "go_string._" + 500 + 26)', 1))
        cases.append(("offset written as a sum", t, False))
        # 24. unchanged copy passes (also the Lean copy)
        t = copy(); leancopy(t)
        cases.append(("unchanged copy", t, True))
        ok = True
        for name, t, expect in cases:
            why = ""
            try:
                conv.CLEANED.clear()
                sh = t / "SHash.lean"
                run(t, lambda s: None,
                    shash=name in ("stale SHash.lean", "hashes only in a comment", "unchanged copy", "SHash suffix .take 0",
                                   "SHash comment inside a string"),
                    goroot=t / "gosrc" if (t / "gosrc").exists() else None,
                    shash_file=sh if sh.exists() else None,
                    lean=t / "lean" if (t / "lean").exists() else None,
                    fmts=[x for x in FMTS if x[1] != "blFmtB"] if name == "blFmtB not registered" else None)
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
