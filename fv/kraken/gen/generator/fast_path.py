"""fast-path: `generator.py encoder --fast-path`, generated fast-path theorems for flat encoders (`MarshalSSZTo`), and for
encoders with pointer fields to a nested container of NESTED_CALLEES (the nested kinds of
`lean/Codec/Kind/EncodeFastPathNestedAnyFrame.lean`; each nested call through the function specification of its callee).

Interface: the encoder step lemmas of `lean/Codec/Encode*.lean` and the statement kinds of `lean/Codec/Kind/`. A symbolic
dataflow walk over the fast path of the `.S` file (head; per IR field its length test not taken, its capacity test
passed with the growslice site SKIPPED, never stepped; the store / `memmove` commit; the epilogue with the frame
test where present) produces ONE module: the head theorem, one theorem per IR field, the epilogue theorem, the
fast-path theorem, each with its `_kind` line (`encodeHeadKindAnyFrame`, `encodeFieldKindAnyFrame`, `encodeEpilogueKindAnyFrame`, `encodeFastPathKindAnyFrame`),
and, on request, the identity with a hand statement (`_statement`).

**Fast path only**: the premises are `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact
length. No growslice branch, length reject or morestack path is proved.

Fail-closed: every check raises `FastPathRefuse`; `generator.encoder_fast_path` is the only caller and returns a text only from
one guarded success point (see there). This module never writes to stdout.
"""
import hashlib, json, pathlib, re

FAST_PATH_IMPORTS = ["Codec.Kind.EncodeFastPathAnyFrame", "Codec.EncodeFrameTest"]
R64 = "rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15".split()
R32 = {"eax": "rax", "ebx": "rbx", "ecx": "rcx", "edx": "rdx", "esi": "rsi", "edi": "rdi"}
BYTE_SIZES = (4, 20, 32, 48, 96)
# the byte vector size whose append is an inline 32-bit copy (`Codec/EncodeInlineCopy.lean`), not a `runtime.memmove` call
INLINE_SIZE = 4
INLINE_IMPORTS = ["Codec.EncodeInlineCopy"]
THEOREM_OPTIONS = "set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\n"
# A pointer field to a nested container whose callee encoder has a fast-path function specification: the callee table.
# `label`: the callee symbol; `code`: its code constant; `holds`: the theorem that proves the specification from the code
# (premises: the placement of the code and `MemmoveContract S`); `size`: the SSZ size; `frame`: the bytes of the callee
# frame below its return slot (the specification names them).
NESTED_CALLEES = {
    "Checkpoint": dict(pkg="github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1",
                       label="github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo",
                       code="Prysm.Checkpoint.Code.marshalSSZTo", holds="Prysm.Checkpoint.Encode.fast_path_function_spec_holds",
                       imports=["Prysm.Checkpoint.Code", "Prysm.Checkpoint.FunctionSpecsAsNestedField"], size=40, frame=120),
}
NESTED_IMPORTS = ["Codec.Kind.EncodeFastPathNestedAnyFrame", "Codec.EncodeNestedCheckpoint"]
NESTED_LAYOUT_FIELDS = ("callees", "goStart", "frame", "guardAddend", "lowExtra", "stackChunkCount", "stackChunkLengths", "pre",
                        "existentials", "post")
# The options of the theorems of a file with nested fields, by role ("" = the defaults). Measured on AttestationData: with
# the defaults, every field theorem fails in the `simp only` of a label fact; head, epilogue and fast-path theorem pass.
NESTED_FIELD_OPTIONS = ("-- Measured cause: with the default maxRecDepth (512), the `simp only` of a label fact (`Machine.label_at'`)\n"
                        "-- fails with \"maximum recursion depth has been reached\"; 1000 passes. The default maxHeartbeats passes.\n"
                        "set_option maxRecDepth 1000 in\n")
NESTED_THEOREM_OPTIONS = dict(head="", field=NESTED_FIELD_OPTIONS, nested=NESTED_FIELD_OPTIONS, epilogue="", fast="")


class FastPathRefuse(Exception):
    """A refusal: the input is outside the interface. `why` is the reason."""

    def __init__(self, why):
        super().__init__(why)
        self.why = why


# ---------------------------------------------------------------- inputs

def read_ir(ir_path, tname):
    """(fields, ssz size, ir sha). fields: (name, kind 'u' | 'b', size, Go offset), IR order. Both IR views (Go
    fields with tags, SSZ IR fields) must agree; anything else is refused."""
    raw = pathlib.Path(ir_path).read_bytes()
    if "." not in tname:
        raise FastPathRefuse(f"type name {tname} is not pkg.Name")
    pkg, name = tname.rsplit(".", 1)
    ts = [t for c in json.loads(raw)["configs"] for t in c.get("types", [])
          if t.get("name") == name and t.get("package", "").endswith("/" + pkg)]
    if len(ts) != 1:
        raise FastPathRefuse(f"type {tname}: {len(ts)} IR entries (need exactly 1)")
    t = ts[0]
    gof = [f for f in t["go_fields"] if f["exported"]]
    irf = t["ir"]["fields"]
    if [f["name"] for f in gof] != [f["key"] for f in irf]:
        raise FastPathRefuse("Go fields and IR fields differ in names or order")
    out = []
    for g, f in zip(gof, irf):
        v = f["v"]
        if v.get("variable"):
            raise FastPathRefuse(f"field {g['name']}: variable size (not a flat field)")
        if v.get("k") == "pointer":
            dt = v.get("delegated_to") or {}
            cal = NESTED_CALLEES.get(dt.get("name"))
            if not (dt.get("k") == "container" and cal and dt.get("pkg") == cal["pkg"]):
                raise FastPathRefuse(f"field {g['name']}: pointer to the nested container {dt.get('name')} "
                                     "(covered: a nested container of NESTED_CALLEES)")
            if not (g["type"] == f"*{cal['pkg']}.{dt['name']}" and g["size_gc_amd64"] == 8 and v.get("go_type") == f"*{dt['name']}"
                    and v.get("fixed_size") == cal["size"] and dt.get("fixed_size") == cal["size"] and not dt.get("variable")):
                raise FastPathRefuse(f"field {g['name']}: pointer field whose IR does not match the callee {dt['name']}")
            out.append((g["name"], "n", cal["size"], g["offset_gc_amd64"], dt["name"]))
            continue
        m = re.search(r'ssz-size:"(\d+)"', g["tag"])
        if m:
            n = int(m[1])
            if not (g["type"] == "[]byte" and v.get("k") == "vector" and v.get("go_type") == "[]byte"
                    and v.get("elem", {}).get("k") == "byte" and v.get("size") == n and v.get("fixed_size") == n
                    and g["size_gc_amd64"] == 24):
                raise FastPathRefuse(f"field {g['name']}: ssz-size tag but not a []byte vector of that size")
            if n not in BYTE_SIZES:
                raise FastPathRefuse(f"field {g['name']}: byte vector of {n} bytes (covered: 4, 20, 32, 48, 96)")
            out.append((g["name"], "b", n, g["offset_gc_amd64"]))
        else:
            u = v.get("underlying") if v.get("k") == "overlay" else v
            if not (g["size_gc_amd64"] == 8 and v.get("fixed_size") == 8 and u and u.get("k") == "uint"
                    and u.get("bits") == 64):
                raise FastPathRefuse(f"field {g['name']}: not an 8-byte uint64 or uint64 overlay (field kind not covered)")
            out.append((g["name"], "u", 8, g["offset_gc_amd64"]))
    if not out:
        raise FastPathRefuse("no fields")
    size = sum(f[2] for f in out)
    if t["ir"].get("variable") or t["ir"].get("fixed_size") != size:
        raise FastPathRefuse(f"IR fixed size {t['ir'].get('fixed_size')} is not the sum of the field sizes {size}")
    return out, size, hashlib.sha256(raw).hexdigest()


def read_S(path, tname):
    raw = pathlib.Path(path).read_bytes()
    lines = [l.strip() for l in raw.decode("ascii").split("\n")]
    while lines and lines[-1] == "":
        lines.pop()
    if any(l == "" for l in lines):
        raise FastPathRefuse("blank line inside the .S file (index = line - 1 would not hold)")
    name = tname.rsplit(".", 1)[1]
    if not lines or not lines[0].endswith(f".{name}.MarshalSSZTo:"):
        raise FastPathRefuse(f"the .S file does not start with the label of {name}.MarshalSSZTo")
    return lines, hashlib.sha256(raw).hexdigest()


def parse_layout(src, name):
    """A hand layout `def <name> : EncoderFrameLayout where …` from a Lean source: the memory order of the `pre` stack chunks
    (offsets from the entry rsp) and their binder indices, plus the whole literal text of the def (normalised)."""
    short = name.rsplit(".", 1)[-1]
    txt = pathlib.Path(src).read_text()
    m = (re.search(rf"\ndef _root_\.{re.escape(name)} : EncoderFrameLayout where\n((?:  .*\n|    .*\n)+)", txt)
         or re.search(rf"\ndef {re.escape(short)} : EncoderFrameLayout where\n((?:  .*\n|    .*\n)+)", txt))
    if not m:
        raise FastPathRefuse(f"hand layout {name} not found in {src}")
    body = m[1]
    flds = {}
    cur = None
    for l in body.split("\n"):
        mm = re.match(r"  (\w+) := (.*)", l)
        if mm:
            cur = mm[1]
            flds[cur] = mm[2]
        elif l.startswith("    ") and cur:
            flds[cur] += " " + l.strip()
    pre = flds.get("pre", "")
    order = [(int(n) * (1 if d == "above" else -1), int(i)) for d, n, i in
             re.findall(r"\.at \(\.(above|below) (\d+)\) \(\.original (\d+)\)", pre)]
    if not order:
        raise FastPathRefuse(f"hand layout {name}: no stack chunks parsed")
    norm = {k: re.sub(r"\s+", " ", v).strip() for k, v in flds.items()}
    return order, norm


# ---------------------------------------------------------------- small text helpers

def num(x):
    return int(x, 16) if x else 0


def lit(n):
    return str(n) if n >= 0 else f"({n})"


def stk(off, base="rsp.toBitVec"):
    return base if off == 0 else f"({base} - {-off})" if off < 0 else f"({base} + {off})"


def v_pf(v, zs=False):
    """bytes term of a slot value; zs: statement context (s.regs.*), else proof context"""
    k = v[0]
    rg = (lambda r: f"s.regs.{r}") if zs else (lambda r: r)
    if k in ("orig", "fld", "ex"):
        return v[1]
    if k == "reg":
        return f"(Int.toBytes 8 {rg(v[1])}.toBitVec.toInt)"
    if k == "len":
        return f"(Int.toBytes 8 ({rg('rcx')}.toBitVec + {v[1]}).toInt)"
    if k == "ret":
        return f"(Int.toBytes 8 (Host.addrOf (k + {v[1]})).toBitVec.toInt)"
    if k == "scr":
        return "scratch"
    if k == "x15":
        b = f"(Int.toBytes 16 ({v[1]}.get (AvxReg.xmm RegMm.mm15)).toInt)"
        return {"full": b, "lo8": f"({b}.take 8)", "hi8": f"({b}.drop 8)"}[v[2]]
    if k == "scrn":
        return v[1]
    if k == "fpv":
        return f"(Int.toBytes 8 ({rg('rsp')}.toBitVec - 8).toInt)"
    if k == "blk":
        return v[1]
    raise FastPathRefuse(f"internal: slot value {v}")


def v_len(v):
    k = v[0]
    if k in ("orig", "fld", "ex", "scrn"):
        return "h" + v[1]
    if k in ("reg", "len", "ret", "fpv"):
        return "(Int.toBytes_length 8 _)"
    if k == "blk":
        return v[2]
    if k == "scr":
        return "hsc"
    if k == "x15":
        return {"full": "(Int.toBytes_length 16 _)", "lo8": "(by rw [List.length_take, Int.toBytes_length]; rfl)",
                "hi8": "(by rw [List.length_drop, Int.toBytes_length])"}[v[2]]
    raise FastPathRefuse(f"internal: slot value {v}")


def v_kind(v):
    k = v[0]
    if k == "orig":
        return f".original {v[2]}"
    if k == "reg":
        return f".reg .{v[1]}"
    if k == "ex":
        return f".existential {v[2]}"
    if k == "fld":
        return f".field {v[2]}"
    if k in ("len", "ret"):
        return f".{k} {v[1]}"
    if k == "scr":
        return ".scratch"
    if k == "fpv":
        return ".framePointer"
    raise FastPathRefuse(f"slot value {v} has no kind form")


def s_pf(v):
    k = v[0]
    if k == "rcv":
        return "rax.toBitVec"
    if k == "ptr":
        return "rbx.toBitVec"
    if k == "cap":
        return "rdi.toBitVec"
    if k == "len":
        return "rcx.toBitVec" if v[1] == 0 else f"(rcx.toBitVec + {v[1]})"
    if k == "fptr":
        return v[1]
    if k == "fval":
        return f"(BitVec.ofInt 64 (Int.ofBytes {v[1]}))"
    if k == "fval32":
        return f"(BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes {v[1]})))"
    if k == "stk":
        return stk(v[1])
    if k == "dst":
        return "(rbx.toBitVec + rcx.toBitVec)" if v[1] == 0 else f"(rbx.toBitVec + rcx.toBitVec + {v[1]})"
    if k == "imm":
        return str(v[1])
    if k == "pfr":
        return f"(rbx.toBitVec - {stk(v[1])})"
    raise FastPathRefuse(f"register value not in the language: {v}")


def s_statement(v):
    k = v[0]
    if k == "rcv":
        return "s.regs.rax.toBitVec"
    if k == "ptr":
        return "s.regs.rbx.toBitVec"
    if k == "cap":
        return "s.regs.rdi.toBitVec"
    if k == "len":
        return "s.regs.rcx.toBitVec" if v[1] == 0 else f"s.regs.rcx.toBitVec + {v[1]}"
    if v == ("imm", 0):
        return "0"
    raise FastPathRefuse(f"live register value not in the boundary language: {v}")


def s_kind(v):
    if v[0] in ("rcv", "ptr", "cap"):
        return "." + {"rcv": "receiver"}.get(v[0], v[0])
    if v[0] == "len":
        return f".len {v[1]}"
    if v == ("imm", 0):
        return ".zero"
    raise FastPathRefuse(f"live register value {v} has no kind form")


PATS = [
    (r"mov %(r\w+),%(r\w+)", lambda m: ("movrr", m[2], m[1])),
    (r"mov (-?0x[0-9a-f]+)?\(%(r\w+)\),%(r\w+)", lambda m: ("ld", m[3], m[2], num(m[1]))),
    (r"mov %(r\w+),(-?0x[0-9a-f]+)?\(%(r\w+)\)", lambda m: ("st", m[1], m[3], num(m[2]))),
    (r"mov %(r\w+),(-?0x[0-9a-f]+)?\(%(r\w+),%(r\w+),1\)", lambda m: ("stidx", m[1], m[3], m[4], num(m[2]))),
    (r"mov (-?0x[0-9a-f]+)?\(%(r\w+)\),%(e[a-z]{2})", lambda m: ("ld32", R32[m[3]], m[2], num(m[1])) if m[3] in R32 else ("other",)),
    (r"mov %(e[a-z]{2}),(-?0x[0-9a-f]+)?\(%(r\w+),%(r\w+),1\)",
     lambda m: ("stidx32", R32[m[1]], m[3], m[4], num(m[2])) if m[1] in R32 else ("other",)),
    (r"mov \$(0x[0-9a-f]+),%(e\w+)", lambda m: ("movi", R32[m[2]], num(m[1]))),
    (r"lea (-?0x[0-9a-f]+)\(%(r\w+)\),%(r\w+)", lambda m: ("lea", m[3], m[2], num(m[1]))),
    (r"lea \(%(r\w+),%(r\w+),1\),%(r\w+)", lambda m: ("leaidx", m[3], m[1], m[2])),
    (r"add \$(-?0x[0-9a-f]+),%(r\w+)", lambda m: ("addi", m[2], num(m[1]))),
    (r"sub \$(-?0x[0-9a-f]+),%(r\w+)", lambda m: ("subi", m[2], num(m[1]))),
    (r"add %(r\w+),%(r\w+)", lambda m: ("addrr", m[2], m[1])),
    (r"sub %(r\w+),%(r\w+)", lambda m: ("subrr", m[2], m[1])),
    (r"cmp %(r\w+),%(r\w+)", lambda m: ("cmprr", m[2], m[1])),
    (r"cmpq \$(0x[0-9a-f]+),(-?0x[0-9a-f]+)?\(%(r\w+)\)", lambda m: ("cmpmi", m[3], num(m[2]), num(m[1]))),
    (r"(jae|jb|jne|jbe|je) (\S+)", lambda m: ("jcc", m[1], m[2])),
    (r"test %(r\w+),%(r\w+)", lambda m: ("test", m[1]) if m[1] == m[2] else ("other",)),
    (r"jmp (\S+)", lambda m: ("jmp", m[1])),
    (r"movups %xmm15,(-?0x[0-9a-f]+)?\(%(r\w+)\)", lambda m: ("movups", m[2], num(m[1]))),
    (r"xor %(e\w+),%(e\w+)", lambda m: ("xor", R32[m[1]]) if m[1] == m[2] else ("other",)),
    (r"callq (\S+)", lambda m: ("call", m[1])),
    (r"push %rbp", lambda m: ("push",)), (r"pop %rbp", lambda m: ("pop",)),
]


# ---------------------------------------------------------------- the walk

class FastPathGenerator:
    """Walk + text of one flat encoder. Construction runs the whole walk (two passes: regions, then emission);
    any doubt raises FastPathRefuse."""

    def __init__(self, S, const, ir, tname, prefix, hand_layout=None, hand_layout_src=None):
        if not re.fullmatch(r"[A-Za-z][A-Za-z0-9]*", const):
            raise FastPathRefuse(f"code constant name {const!r} is not a bare identifier")
        if not re.fullmatch(r"(?:[A-Z][A-Za-z0-9]*\.)?[a-z][a-z0-9_]*", prefix):
            raise FastPathRefuse(f"prefix {prefix!r} is not a lower-case identifier (optionally behind one capitalized word)")
        self.t, self.C, self.px = tname.rsplit(".", 1)[1], const, prefix
        self.fields, self.size, self.irsha = read_ir(ir, tname)
        self.L, self.Ssha = read_S(S, tname)
        self.lab = {}
        for i, l in enumerate(self.L):
            if l.endswith(":"):
                if l[:-1] in self.lab:
                    raise FastPathRefuse(f"label {l[:-1]} defined twice")
                self.lab[l[:-1]] = i
        go0 = self.fields[0][3]
        if go0 not in (0, 8):
            raise FastPathRefuse(f"first Go offset {go0} (covered: 0, 8)")
        self.st = go0 == 8
        self.nested = any(f[1] == "n" for f in self.fields)
        self.vn = [f"v{i}" if f[1] == "u" else f"b{i}" if f[1] == "b" else f"ep{i}" for i, f in enumerate(self.fields)]
        self.bidx = [i for i, f in enumerate(self.fields) if f[1] == "b"]
        self.uidx = [i for i, f in enumerate(self.fields) if f[1] == "u"]
        self.nidx = [i for i, f in enumerate(self.fields) if f[1] == "n"]
        self.pn = {i: f"p{i}" for i in self.bidx + self.nidx}
        # the SSZ leaves: a nested field is its epoch (8 bytes) and its root (32 bytes); leaf[i] = index of the first leaf of field i
        self.leaf, nl = [], 0
        for f in self.fields:
            self.leaf.append(nl)
            nl += 2 if f[1] == "n" else 1
        if self.nested:
            cs = {f[4] for f in self.fields if f[1] == "n"}
            if len(cs) != 1:
                raise FastPathRefuse(f"nested fields of more than one callee type {sorted(cs)}")
            self.callee = NESTED_CALLEES[cs.pop()]
            self.cfr = self.callee["frame"]
            if hand_layout:
                raise FastPathRefuse("a hand layout is not covered with nested fields")
        g, o = (8 if self.st else 0), 0
        self.goff, self.soff = [], []
        for (n, k, sz, go, *_) in self.fields:
            if go != g:
                raise FastPathRefuse(f"Go offsets are not the running sum (field {n}: {go}, expected {g})")
            self.goff.append(g)
            self.soff.append(o)
            g += 24 if k == "b" else 8
            o += sz
        self.hand = None
        if hand_layout:
            self.hand = (hand_layout,) + parse_layout(hand_layout_src, hand_layout)
        self.walk()

    def losz(self):
        """the size key of the low block in the entry state: `S` (memmove scratch) or `SE` (`S` + the callee frame)"""
        return "SE" if self.nested else "S"

    def lab_of(self, name):
        if name not in self.lab:
            raise FastPathRefuse(f"jump to a label not in the file: {name}")
        return self.lab[name]

    def ins(self, i):
        if not (0 <= i < len(self.L)):
            raise FastPathRefuse(f"directive {i}: outside the file (truncated?)")
        l = self.L[i]
        m = re.fullmatch(r"(\S+):", l)
        if m:
            return ("label", m[1])
        if l == "nop":
            return ("nop",)
        if l == "retq":
            return ("ret",)
        for pat, f in PATS:
            m = re.fullmatch(pat, l)
            if m:
                r = f(m)
                if r[0] == "other":
                    return ("other", l)
                for x in r[1:]:
                    if isinstance(x, str) and x.startswith("r") and x not in R64 and not x.startswith("runtime"):
                        return ("other", l)
                return r
        return ("other", l)

    # ---------- emission helpers ----------
    def win(self, i, n=1):
        a = i - self.pend
        self.pend = 0
        return a, f"(k + {a}) (k + {i + n}) (window_infix_at hk {a} {i + n - a}) (by rfl) (by rfl)"

    def E(self, s):
        if self.emit:
            self.out.append("  " + s)

    def newH(self):
        self.hn += 1
        self.H = f"H{self.hn}"
        self.mem_ = f"m{self.hn}"
        return f"m{self.hn}", self.H

    def setreg(self, r, v, actual, tac="bv_omega"):
        self.reg[r] = v
        self.E(f"apply register_value_rewrite Reg64.{r} {s_pf(v)} _ _ _ (by show ({actual} : BitVec 64) = {s_pf(v)}; {tac})")
        self.E("normalize_registers")

    def slot_at(self, off, size):
        for i, (o, sz, v) in enumerate(self.slots):
            if o == off and sz == size:
                return i
        return None

    def label_hyp(self, j):
        if j not in self.hl:
            self.hl.add(j)
            self.E(f"have hl{j} := Machine.label_at' hk hf (j := {j})")
            self.E(f"  (by simp only [{self.C}, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)")
            self.E(f"  (by simp only [{self.C}, List.take_succ_cons, List.take_zero, List.contains_cons, "
                   "List.contains_nil]; decide)")
        return f"hl{j}"

    def walk(self):
        L = self.L
        if self.ins(0)[0] != "label" or self.ins(1)[0] != "label":
            raise FastPathRefuse("prologue form: directives 0 and 1 must be labels")
        i2 = self.ins(2)
        if i2 == ("other", "cmp 0x10(%r14),%rsp") and self.ins(3)[:2] == ("jcc", "jbe"):
            self.gd, npro = 0, 6
            self.lab_of(self.ins(3)[2])
        else:
            m = re.fullmatch(r"lea -0x([0-9a-f]+)\(%rsp\),%r12", L[2])
            if not (m and self.ins(3) == ("other", "cmp 0x10(%r14),%r12") and self.ins(4)[:2] == ("jcc", "jbe")):
                raise FastPathRefuse("prologue guard form")
            self.gd, npro = int(m[1], 16), 7
            self.lab_of(self.ins(4)[2])
            if self.gd == 0:
                raise FastPathRefuse("prologue guard form (lea of 0)")
        if self.ins(npro - 2) != ("push",) or self.ins(npro - 1) != ("movrr", "rbp", "rsp"):
            raise FastPathRefuse("prologue form (push %rbp; mov %rsp,%rbp)")
        a = self.ins(npro)
        if a[0] == "subi" and a[1] == "rsp" and a[2] > 0:
            self.F = a[2]
        elif a[0] == "addi" and a[1] == "rsp" and a[2] < 0:
            self.F = -a[2]
        else:
            raise FastPathRefuse("frame allocation form")
        if self.F % 8 or self.F < 16 or self.F > 4096:
            raise FastPathRefuse(f"frame size {self.F}")
        if self.gd and self.gd > self.F:
            raise FastPathRefuse(f"large-frame guard {self.gd} larger than the frame {self.F}")
        if self.nested:
            # the guard premise covers the frame, the callee return slot and the callee frame below it
            self.ga = self.F + 16 + self.cfr
        self.npro = npro
        calls = [l[6:] for l in L if l.startswith("callq ")]
        self.rt = "runtime.memmove" in calls
        self.pre = None
        self.run(emit=False)
        touched = self.touched
        offs = [o for o, _ in touched]
        sz = dict(touched)
        rs = -(self.F + 16)
        if self.rt != self.called:
            raise FastPathRefuse("memmove in the file but not on the walked path (or the converse)")
        if self.hand:
            hname, order, _ = self.hand
            mem = [o for o, _ in order]
            bidx = [b for _, b in order]
            if sorted(mem) != sorted(offs) or sorted(bidx) != list(range(len(mem))):
                raise FastPathRefuse(f"hand layout {hname}: slots {sorted(mem)} != walked {sorted(offs)}")
            bind = [o for o, _ in sorted(order, key=lambda x: x[1])]
            self.layname = hname
        else:
            ups = sorted(o for o in offs if o > 0)
            mem = [-8] + ups + [o for o in offs if o < 0 and o not in (-8, rs)] + ([rs] if rs in offs else [])
            if sorted(mem) != sorted(offs):
                raise FastPathRefuse("internal: chunk order is not a permutation of the touched regions")
            bind = mem
            self.layname = None

        def nm(o):
            if o == -8:
                return "fp"
            if o > 0:
                return f"s{o // 8}"
            if o == rs:
                return "rslot"
            return f"{'t' if sz[o] == 16 else 'l'}{-o}"
        self.bind = [(o, sz[o], nm(o)) for o in bind]
        if len({x[2] for x in self.bind}) != len(self.bind):
            raise FastPathRefuse("internal: chunk names collide")
        self.pre = [(o, sz[o], ("orig", nm(o), bind.index(o))) for o in mem]
        self.run(emit=True)
        if self.hand:
            mine = self.layout_fields()
            theirs = self.hand[2]
            for k in ("stateWord", "frame", "guardAddend", "callsMemmove", "stackChunkCount", "stackChunkLengths", "pre", "existentials", "post"):
                if mine[k] != theirs.get(k):
                    raise FastPathRefuse(f"hand layout {self.hand[0]}: field {k} is {theirs.get(k)!r}, walked {mine[k]!r}")

    def run(self, emit):
        self.emit = emit
        self.out = []
        self.touched = []
        self.thms = []
        self.hn = 0
        self.hl = set()
        self.pend = 0
        self.exseq = 0
        self.zm = "zmms"
        self.ncall = 0
        self.called = False
        self.ended = False
        self.frametested = False
        self.lenok = set()
        self.capok = None
        self.nilok = None
        self.callfi = None
        self.hcth = False
        F = self.F
        self.reg = {"rax": ("rcv",), "rbx": ("ptr",), "rcx": ("len", 0), "rdi": ("cap",)}
        self.slots = list(self.pre) if self.pre else []
        if (self.pre and (self.rt or self.nested)) or not emit:
            self.slots.append(("lo", self.losz(), ("scr",)))
        self.done = 0
        self.outv = [("d", i) for i in range(len(self.fields))]
        if not emit:
            self.touch(-8, 8, push=True)
        n = self.npro
        self.H = "h_mem"
        self.mem_ = "mem"
        pro = "encoder_prologue_small_frame _ _ _" if self.gd == 0 else f"encoder_prologue_large_frame _ _ _ ({-self.gd}) {self.gd}"
        extra = "" if self.gd == 0 else " (by rfl)"
        self.E(f"apply {pro} _ k (k + {n}) (window_infix_at hk 0 {n}) (by rfl) (by rfl){extra} guard fp hfp _ _ _ "
               "(by dsimp only; ecancel) " + ("(by dsimp only; omega)" if self.nested else "hguard"))
        m, H = self.newH()
        self.E(f"intro {m} {H} fl{self.hn}; normalize_registers; dsimp only at {H}")
        self.setslot(-8, 8, ("reg", "rbp"))
        a = self.ins(n)
        _, w = self.win(n)
        self.E(f"apply {'step_sub_immediate' if a[0] == 'subi' else 'step_add_immediate'} Reg64.rsp {lit(a[2])} _ {w}")
        self.E("intro fl; normalize_registers")
        self.reg["rsp"] = ("stk", -8)
        self.setreg("rsp", ("stk", -(F + 8)), f"(rsp.toBitVec - 8) {'-' if a[0] == 'subi' else '+'} {lit(a[2])}")
        i = n + 1
        while self.ins(i)[0] == "st" and self.ins(i)[2] == "rsp" and self.ins(i)[3] - (F + 8) > 0:
            self.step(i)
            i += 1
        self.start = i
        self.cut = [i]
        self.bstate = [self.boundary(i)]
        steps = 0
        while True:
            steps += 1
            if steps > 2000:
                raise FastPathRefuse("walk does not end")
            a = self.ins(i)
            if a[0] == "nop":
                self.pend += 1
                i += 1
                continue
            if a == ("pop",):
                if self.done != len(self.fields):
                    raise FastPathRefuse(f"return reached after {self.done} of {len(self.fields)} fields")
                self.epilogue(i)
                return
            nd = self.done
            i = self.step(i)
            if self.done != nd:
                if self.pend:
                    raise FastPathRefuse("internal: pending nops at a commit")
                self.cut.append(i)
                self.bstate.append(self.boundary(i))

    def touch(self, off, size, push=False, call=False):
        """first touch of a stack region: inside the frame, the home slots, the saved rbp (push) or the memmove
        return slot (call) only; no partial overlap with an earlier region."""
        F = self.F
        ok = (-(F + 8) <= off and off + size <= -8) or (8 <= off and off + size <= 40) \
            or (push and off == -8 and size == 8) or (call and off == -(F + 16) and size == 8)
        if not ok:
            raise FastPathRefuse(f"stack access at {off} (size {size}) outside the frame / home slots")
        for o, sz in self.touched:
            if o <= off and off + size <= o + sz:
                return
            if not (off + size <= o or o + sz <= off):
                raise FastPathRefuse(f"overlapping stack regions ({o}, {sz}) and ({off}, {size})")
        self.touched.append((off, size))
        self.slots.insert(len(self.slots) - 1, (off, size, ("orig", "q", 0)))

    def setslot(self, off, size, v):
        i = self.slot_at(off, size)
        if i is None:
            raise FastPathRefuse(f"store to a slot that is not whole: {off} {size}")
        self.slots[i] = (off, size, v)

    def getslot(self, off, size):
        i = self.slot_at(off, size)
        if i is None:
            raise FastPathRefuse(f"slot {off} {size} not known")
        return self.slots[i][2]

    def addr_of(self, r, d):
        v = self.reg.get(r)
        if v is None:
            raise FastPathRefuse(f"base register {r} has no known value")
        if v[0] == "stk":
            return ("stk", v[1] + d)
        if v[0] == "rcv":
            return ("rcvw", d)
        raise FastPathRefuse(f"memory operand base {r} = {v} (only the frame or the receiver)")

    def known(self, r):
        if r not in self.reg:
            raise FastPathRefuse(f"read of {r} without a known value")
        return self.reg[r]

    def step(self, i):
        """one directive (or a compare-and-branch pair) of the fast path; returns the next index"""
        a = self.ins(i)
        k = a[0]
        E = self.E
        emit = self.emit
        if k == "label":
            _, w = self.win(i)
            E(f"apply step_label _ _ {w}")
            return i + 1
        if k == "movrr":
            _, rd, rs = a
            v = self.known(rs)
            if rd in ("rsp", "rbp") or rs in ("rsp", "rbp"):
                raise FastPathRefuse(f"move of {rs} to {rd} (frame registers)")
            _, w = self.win(i)
            E(f"apply step_move_register Reg64.{rd} Reg64.{rs} _ {w}")
            E("normalize_registers")
            self.reg[rd] = v
            return i + 1
        if k == "movi":
            _, rd, im = a
            _, w = self.win(i)
            E(f"apply step_move_immediate Reg64.{rd} {im} _ {w}")
            E("normalize_registers")
            self.setreg(rd, ("imm", im), f"BitVec.zeroExtend 64 (BitVec.truncate 32 ({im} : BitVec 64))", "decide")
            return i + 1
        if k == "lea":
            _, rd, rb, d = a
            v = self.reg.get(rb)
            if rd in ("rsp", "rbp"):
                raise FastPathRefuse(f"lea into {rd}")
            if v and v[0] == "len":
                nv = ("len", v[1] + d)
                if nv[1] < 0:
                    raise FastPathRefuse("length minus a constant")
            elif v and v[0] == "stk":
                nv = ("stk", v[1] + d)
            else:
                raise FastPathRefuse(f"lea base {rb} = {v}")
            _, w = self.win(i)
            E(f"apply step_lea Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
            E("normalize_registers")
            self.setreg(rd, nv, f"{s_pf(v)} + {lit(d)}")
            return i + 1
        if k == "addi":
            _, rd, d = a
            v = self.reg.get(rd)
            if rd == "rbp" or not (v and v[0] in ("len", "stk")) or (v[0] == "len" and v[1] + d < 0):
                raise FastPathRefuse(f"add to {rd} = {v}")
            nv = (v[0], v[1] + d)
            if rd == "rsp" and (nv != ("stk", -8) or self.done != len(self.fields)):
                raise FastPathRefuse("rsp changed other than by the frame release after the last field")
            _, w = self.win(i)
            E(f"apply step_add_immediate Reg64.{rd} {lit(d)} _ {w}")
            E("intro fl; normalize_registers")
            self.setreg(rd, nv, f"{s_pf(v)} + {lit(d)}")
            return i + 1
        if k == "subi":
            _, rd, d = a
            v = self.reg.get(rd)
            if rd == "rbp" or not (v and v[0] == "stk"):
                raise FastPathRefuse(f"sub from {rd} = {v}")
            nv = ("stk", v[1] - d)
            if rd == "rsp" and (nv != ("stk", -8) or self.done != len(self.fields)):
                raise FastPathRefuse("rsp changed other than by the frame release after the last field")
            _, w = self.win(i)
            E(f"apply step_sub_immediate Reg64.{rd} {lit(d)} _ {w}")
            E("intro fl; normalize_registers")
            self.setreg(rd, nv, f"{s_pf(v)} - {lit(d)}")
            return i + 1
        if k in ("leaidx", "addrr"):
            if k == "leaidx":
                _, rd, r1, r2 = a
            else:
                _, rd, r2 = a
                r1 = rd
            if rd in ("rsp", "rbp"):
                raise FastPathRefuse(f"{k} into {rd}")
            v1, v2 = self.reg.get(r1), self.reg.get(r2)
            ks = {v1 and v1[0], v2 and v2[0]}
            if ks != {"ptr", "len"}:
                raise FastPathRefuse(f"{k}: operands {v1} {v2} are not (dst pointer, length)")
            nv = ("dst", (v1 if v1[0] == "len" else v2)[1])
            _, w = self.win(i)
            if k == "leaidx":
                E(f"apply step_lea_indexed Reg64.{rd} Reg64.{r1} Reg64.{r2} _ {w}")
                E("normalize_registers")
            else:
                E(f"apply step_add_registers Reg64.{rd} Reg64.{r2} _ {w}")
                E("intro fl; normalize_registers")
            self.setreg(rd, nv, f"{s_pf(v1)} + {s_pf(v2)}")
            return i + 1
        if k == "subrr":
            _, rd, rs = a
            vd, vs = self.reg.get(rd), self.reg.get(rs)
            sp = -(self.F + 8)
            if rd in ("rsp", "rbp") or vs != ("stk", sp):
                raise FastPathRefuse(f"sub of {rs} = {vs}")
            if vd == ("ptr",):
                nv = ("pfr", sp)
            elif vd and vd[0] == "stk":
                nv = ("imm", vd[1] - sp)
            else:
                raise FastPathRefuse(f"sub from {rd} = {vd}")
            _, w = self.win(i)
            E(f"apply step_sub_registers Reg64.{rd} Reg64.{rs} _ {w}")
            E("intro fl; normalize_registers")
            self.setreg(rd, nv, f"{s_pf(vd)} - {stk(sp)}")
            return i + 1
        if k == "xor":
            _, w = self.win(i)
            E(f"apply step_xor32 Reg64.{a[1]} _ {w}")
            E("intro fl; normalize_registers")
            self.reg[a[1]] = ("imm", 0)
            return i + 1
        if k == "st":
            _, rs, rb, d = a
            ad = self.addr_of(rb, d)
            if ad[0] != "stk":
                raise FastPathRefuse("store through the receiver")
            off = ad[1]
            v = self.known(rs)
            if not emit:
                self.touch(off, 8)
            sv = {"rcv": ("reg", "rax"), "ptr": ("reg", "rbx"), "cap": ("reg", "rdi")}.get(v[0])
            if v[0] == "len":
                sv = ("reg", "rcx") if v[1] == 0 else ("len", v[1])
            if v[0] == "fval":
                sv = ("fld", v[1], self.leaf[v[2]], v[2]) if self.nested else ("fld", v[1], v[2])
            if sv is None:
                raise FastPathRefuse(f"stored value not in the slot language: {v}")
            if self.slot_at(off, 8) is None:
                j = self.slot_at(off, 16)
                if j is None or self.slots[j][2][0] != "x15" or self.slots[j][2][2] != "full":
                    raise FastPathRefuse(f"8-byte store at {off} into an unknown chunk")
                z = self.slots[j][2]
                E(f"rw [Machine.at_split16 _ (Int.toBytes_length 16 _) {stk(off)}, "
                  f"show {stk(off)} + 8 = {stk(off + 8)} by bv_omega] at {self.H}")
                self.slots[j:j + 1] = [(off, 8, ("x15", z[1], "lo8", z[3])), (off + 8, 8, ("x15", z[1], "hi8", z[3]))]
            old = self.getslot(off, 8)
            _, w = self.win(i)
            E(f"apply step_store Reg64.{rs} Reg64.{rb} {lit(d)} _ {w}")
            E(f"  {s_pf(self.reg[rb])} {stk(off)} (by encoder_address_equation) {v_pf(old)} {v_len(old)} _ _ _ (by rfl) (by ecancel)")
            m, H = self.newH()
            E(f"intro {m} {H}; normalize_registers; simp only [Reg64s.get64] at {H}")
            if v[0] == "fval":
                E(f"simp only [toBytes_ofInt_ofBytes 64 8 rfl {v[1]} h{v[1]}] at {H}")
            self.setslot(off, 8, sv)
            return i + 1
        if k == "movups":
            _, rb, d = a
            ad = self.addr_of(rb, d)
            if ad[0] != "stk":
                raise FastPathRefuse("movups target is not in the frame")
            off = ad[1]
            if not emit:
                self.touch(off, 16)
            old = self.getslot(off, 16)
            _, w = self.win(i)
            E(f"apply step_store_xmm15 Reg64.{rb} {lit(d)} _ {w}")
            E(f"  {s_pf(self.reg[rb])} {stk(off)} (by encoder_address_equation) {v_pf(old)} {v_len(old)} _ _ _ (by rfl) (by ecancel)")
            m, H = self.newH()
            E(f"intro {m} {H}; normalize_registers; try dsimp only at {H}")
            self.exseq += 1
            self.setslot(off, 16, ("x15", self.zm, "full", self.exseq))
            return i + 1
        if k == "ld":
            _, rd, rb, d = a
            if rd in ("rsp", "rbp"):
                raise FastPathRefuse(f"load into {rd}")
            ad = self.addr_of(rb, d)
            if ad[0] == "stk":
                off = ad[1]
                sv = self.getslot(off, 8)
                val = {"rax": ("rcv",), "rbx": ("ptr",), "rdi": ("cap",), "rcx": ("len", 0)}.get(sv[1]) \
                    if sv[0] == "reg" else ("len", sv[1]) if sv[0] == "len" else None
                _, w = self.win(i)
                if val is not None:
                    E(f"apply step_load_value Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
                    E(f"  {s_pf(self.reg[rb])} {stk(off)} {s_pf(val)} (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)")
                elif sv[0] == "fld":
                    val = ("fval", sv[1], sv[3] if len(sv) > 3 else sv[2])
                    E(f"apply step_load_bytes Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
                    E(f"  {s_pf(self.reg[rb])} {stk(off)} (by encoder_address_equation) {sv[1]} h{sv[1]} _ _ _ (by rfl) (by ecancel)")
                else:
                    raise FastPathRefuse(f"load of a slot whose value is not usable: {sv}")
                E("normalize_registers")
                self.reg[rd] = val
                return i + 1
            go = ad[1]
            for fi, (nm, fk, sz, g, *_) in enumerate(self.fields):
                if g == go:
                    break
            else:
                raise FastPathRefuse(f"receiver load at Go offset {go} is not a field word")
            ra = "rax.toBitVec" if go == 0 else f"(rax.toBitVec + {go})"
            _, w = self.win(i)
            if fk == "u":
                val = ("fval", self.vn[fi], fi)
                E(f"apply step_load_bytes Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
                E(f"  rax.toBitVec {ra} (by encoder_address_equation) {self.vn[fi]} h{self.vn[fi]} _ _ _ (by rfl) (by ecancel)")
            else:
                val = ("fptr", self.pn[fi], fi)
                E(f"apply step_load_value Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
                E(f"  rax.toBitVec {ra} {self.pn[fi]} (by encoder_address_equation) _ _ _ (by rfl) (by ecancel)")
            E("normalize_registers")
            self.reg[rd] = val
            return i + 1
        if k == "cmpmi":
            _, rb, d, im = a
            j = i + 1
            while self.ins(j)[0] == "nop":
                j += 1
            b = self.ins(j)
            if b[:2] != ("jcc", "jne"):
                raise FastPathRefuse("length test form unknown")
            self.lab_of(b[2])
            ad = self.addr_of(rb, d)
            fi = self.done
            if im == 0 and fi < len(self.fields) and self.fields[fi][1] == "n":
                return self.nil_test(i, j, b, rb, d, ad, fi)
            if fi >= len(self.fields) or self.fields[fi][1] != "b" or ad != ("rcvw", self.goff[fi] + 8) \
                    or im != self.fields[fi][2]:
                raise FastPathRefuse("length test is not the current field's length word against its IR size")
            if emit:
                _, w = self.win(i, j - i + 1)
                E(f"apply step_length_check Reg64.{rb} {lit(d)} {im} _ _ {w}")
                E(f"  rax.toBitVec (rax.toBitVec + {ad[1]}) (by encoder_address_equation) (Int.toBytes 8 {im}) (by rfl) (by decide) "
                  "_ _ _ (by rfl) (by ecancel)")
                E("intro fl; normalize_registers")
            else:
                self.pend = 0
            self.lenok.add(fi)
            return j + 1
        if k == "cmprr":
            _, rc, rn = a
            j = i + 1
            while self.ins(j)[0] == "nop":
                j += 1
            b = self.ins(j)
            vc, vn = self.reg.get(rc), self.reg.get(rn)
            if vc and vc[0] == "pfr":
                return self.frametest(i, j, b, rc, rn, vc, vn)
            fi = self.done
            if fi >= len(self.fields):
                raise FastPathRefuse("capacity test after the last field")
            need = self.soff[fi] + self.fields[fi][2]
            if not (vc == ("cap",) and vn and vn[0] == "len" and vn[1] == need):
                raise FastPathRefuse(f"capacity test not provably passed: cmp {rn}={vn}, {rc}={vc} (need len + {need})")
            hle = f"(by show ({s_pf(vn)} : BitVec 64).toNat ≤ (rdi.toBitVec).toNat; bv_omega)"
            if b[:2] == ("jcc", "jae"):
                jl = self.lab_of(b[2])
                if jl <= j:
                    raise FastPathRefuse("capacity test jumps backwards")
                if any(self.L[x] == "callq runtime.growslice" for x in range(jl, jl + 1)):
                    raise FastPathRefuse("capacity test target is the growslice site")
                if not any(self.L[x] == "callq runtime.growslice" for x in range(j + 1, jl)):
                    raise FastPathRefuse("capacity test skips no growslice site")
                hl = self.label_hyp(jl)
                a0 = i - self.pend
                self.pend = 0
                E(f"apply step_cmp_jae_taken Reg64.{rc} Reg64.{rn} _ _ (k + {a0}) (k + {jl}) "
                  f"(window_infix_at hk {a0} {j + 1 - a0}) (by rfl) {hl} _ _ {hle}")
                E("intro fl; normalize_registers")
                self.capok = fi
                return jl
            if b[:2] == ("jcc", "jb"):
                jl = self.lab_of(b[2])
                if not any(self.L[x] == "callq runtime.growslice" for x in range(jl, min(jl + 12, len(self.L)))):
                    raise FastPathRefuse("capacity test (jb) target is not a growslice block")
                _, w = self.win(i, j - i + 1)
                E(f"apply step_cmp_jb_not_taken Reg64.{rc} Reg64.{rn} _ _ {w} _ _ {hle}")
                E("intro fl; normalize_registers")
                self.capok = fi
                return j + 1
            raise FastPathRefuse("capacity test branch form unknown")
        if k == "jmp":
            jl = self.lab_of(a[1])
            if jl <= i:
                raise FastPathRefuse("backward jump on the walked path")
            hl = self.label_hyp(jl)
            a0 = i - self.pend
            self.pend = 0
            E(f"apply step_jump _ _ (k + {a0}) (k + {jl}) (window_infix_at hk {a0} {i + 1 - a0}) (by rfl) {hl}")
            return jl
        if k == "stidx":
            _, rs, rb, ri, d = a
            vb, vi, v = self.reg.get(rb), self.reg.get(ri), self.reg.get(rs)
            if {vb and vb[0], vi and vi[0]} != {"ptr", "len"}:
                raise FastPathRefuse(f"indexed store base / index {vb} {vi}")
            fi = self.done
            if fi >= len(self.fields):
                raise FastPathRefuse("output store after the last field")
            o = (vb if vb[0] == "len" else vi)[1] + d
            if self.fields[fi][1] != "u" or o != self.soff[fi] or not (v and v[0] == "fval" and v[2] == fi):
                raise FastPathRefuse(f"indexed store is not the current uint64 field at its SSZ offset ({o}, {v})")
            if self.capok != fi:
                raise FastPathRefuse(f"output store of field {fi} without its capacity test")
            _, w = self.win(i)
            E(f"apply step_store_indexed Reg64.{rs} Reg64.{rb} Reg64.{ri} {lit(d)} _ {w}")
            E(f"  {s_pf(vb)} {s_pf(vi)} {s_pf(('dst', o))} (by encoder_address_equation) d{fi} hd{fi} _ _ _ (by rfl) (by rfl) (by ecancel)")
            m, H = self.newH()
            E(f"intro {m} {H}; normalize_registers; simp only [Reg64s.get64] at {H}")
            E(f"simp only [toBytes_ofInt_ofBytes 64 8 rfl {v[1]} h{v[1]}] at {H}")
            self.outv[fi] = ("v", fi)
            self.done += 1
            return i + 1
        if k == "ld32":
            _, rd, rb, d = a
            fi = self.done
            v = self.reg.get(rb)
            if rd in ("rsp", "rbp") or fi >= len(self.fields) or self.fields[fi][1] != "b" or self.fields[fi][2] != INLINE_SIZE \
                    or v != ("fptr", self.pn[fi], fi) or d != 0:
                raise FastPathRefuse(f"32-bit load `{self.L[i]}` is not the load of the current 4-byte field through its pointer ({v})")
            if fi not in self.lenok:
                raise FastPathRefuse(f"32-bit load of field {fi} without its length test")
            _, w = self.win(i)
            E(f"apply step_load_bytes32 Reg64.{rd} Reg64.{rb} {lit(d)} _ {w}")
            E(f"  {self.pn[fi]} {self.pn[fi]} (by encoder_address_equation) {self.vn[fi]} h{self.vn[fi]} _ _ _ (by rfl) (by ecancel)")
            E("normalize_registers")
            self.reg[rd] = ("fval32", self.vn[fi], fi)
            return i + 1
        if k == "stidx32":
            _, rs, rb, ri, d = a
            vb, vi, v = self.reg.get(rb), self.reg.get(ri), self.reg.get(rs)
            if {vb and vb[0], vi and vi[0]} != {"ptr", "len"}:
                raise FastPathRefuse(f"indexed store base / index {vb} {vi}")
            fi = self.done
            if fi >= len(self.fields):
                raise FastPathRefuse("output store after the last field")
            o = (vb if vb[0] == "len" else vi)[1] + d
            if self.fields[fi][1] != "b" or self.fields[fi][2] != INLINE_SIZE or o != self.soff[fi] \
                    or v != ("fval32", self.vn[fi], fi):
                raise FastPathRefuse(f"32-bit indexed store is not the current 4-byte field at its SSZ offset ({o}, {v})")
            if fi not in self.lenok:
                raise FastPathRefuse(f"output store of field {fi} without its length test")
            if self.capok != fi:
                raise FastPathRefuse(f"output store of field {fi} without its capacity test")
            _, w = self.win(i)
            E(f"apply step_store_indexed32 Reg64.{rs} Reg64.{rb} Reg64.{ri} {lit(d)} _ {w}")
            E(f"  {s_pf(vb)} {s_pf(vi)} {s_pf(('dst', o))} (by encoder_address_equation) d{fi} hd{fi} _ _ _ (by rfl) (by rfl) (by ecancel)")
            m, H = self.newH()
            E(f"intro {m} {H}; normalize_registers; simp only [Reg64s.get64] at {H}")
            E(f"simp only [Machine.zx32, toBytes_ofInt_ofBytes 32 4 rfl {self.vn[fi]} h{self.vn[fi]}] at {H}")
            self.outv[fi] = ("v", fi)
            self.done += 1
            return i + 1
        if k == "call" and self.nested and a[1] == self.callee["label"]:
            return self.nested_call(i)
        if k == "test":
            return self.test_branch(i, a)
        if k == "call":
            if a[1] != "runtime.memmove":
                raise FastPathRefuse(f"call of {a[1]} on the walked path (callee encoder without a proved theorem)")
            fi = self.done
            F = self.F
            if fi >= len(self.fields) or self.fields[fi][1] != "b":
                raise FastPathRefuse("memmove for a field that is not a byte vector")
            if fi not in self.lenok:
                raise FastPathRefuse(f"memmove of field {fi} without its length test")
            if self.capok != fi:
                raise FastPathRefuse(f"memmove of field {fi} without its capacity test")
            vr = (self.reg.get("rax"), self.reg.get("rbx"), self.reg.get("rcx"))
            if vr != (("dst", self.soff[fi]), ("fptr", self.pn[fi], fi), ("imm", self.fields[fi][2])):
                raise FastPathRefuse(f"memmove arguments {vr}")
            rs = -(F + 16)
            self.called = True
            if not emit:
                self.touch(rs, 8, call=True)
            if self.pend:
                E(f"apply step_nops _ (k + {i - self.pend}) (k + {i}) (window_infix_at hk {i - self.pend} {self.pend}) (by rfl) (by rfl)")
                self.pend = 0
            old, lo = self.getslot(rs, 8), self.getslot("lo", self.losz())
            self.ncall += 1
            c = self.ncall
            blk = lo
            if self.nested:
                # the scratch of memmove is the top `S` bytes of the low block (`S` + the callee frame)
                if self.slot_at("lo", "SE") is None:
                    raise FastPathRefuse("memmove after a nested call (the low block is split)")
                E(f"obtain ⟨lm{c}, sm{c}, hlm{c}, hsm{c}, Hm{c}⟩ := low_block_memmove_split {stk(-(F + 16 + self.cfr))} {stk(rs)} S {self.cfr}")
                E(f"  hS (by decide) (by bv_omega) {v_pf(lo)} {v_len(lo)} _ _ (by first | ecancel | (dsimp only; ecancel))")
                E(f"clear {self.H}")
                self.H = f"Hm{c}"
                lo = ("scrn", f"sm{c}", None, None)
            E(f"refine eventually_trans _ _ _ _ (encode_memmove_call (k + {i}) (window_infix_at hk {i} 1) {stk(-(F + 8))} "
              f"{s_pf(('dst', self.soff[fi]))} {self.pn[fi]}")
            E(f"  {stk(rs)} ({stk(rs)[1:-1]} - BitVec.ofNat 64 S) S (by bv_omega) "
              f"(Codec.frame_low_address_without_calls rsp.toBitVec {F + 8} {F + 16} S (by decide))")
            E(f"  {self.vn[fi]} d{fi} {v_pf(old)} {v_pf(lo)} (by rw [hd{fi}, h{self.vn[fi]}]) {v_len(old)} {v_len(lo)}")
            E(f"  _ _ (by rfl) (by rfl) (by rfl) (by rw [h{self.vn[fi]}]; rfl) (by first | ecancel | (dsimp only; ecancel)) hmm) ?_")
            E(f"rintro ⟨e{c}, pc{c}⟩ ⟨hpc{c}, hrsp{c}, hrbp{c}, hr14{c}, scr{c}, hscr{c}, Hc{c}⟩")
            E(f"dsimp only at hpc{c} hrsp{c} hrbp{c} hr14{c} Hc{c}")
            E(f"subst hpc{c}")
            rn = ", ".join(f"{r}c{c}" for r in R64)
            E(f"obtain ⟨⟨{rn}⟩, zmmsc{c}, flagsc{c}, memc{c}⟩ := e{c}")
            E(f"simp only at hrsp{c} hrbp{c} hr14{c} Hc{c}")
            E(f"subst rspc{c} rbpc{c} r14c{c}")
            E(f"rw [show k + {i} + 1 = k + {i + 1} from rfl] at Hc{c}")
            self.H = f"Hc{c}"
            self.mem_ = f"memc{c}"
            self.zm = f"zmmsc{c}"
            self.setslot(rs, 8, ("ret", i + 1))
            seq = blk[3] if blk[0] in ("ex", "scrn", "blk") else None
            if seq is None:
                self.exseq += 1
                seq = self.exseq
            if self.nested:
                E(f"obtain ⟨hj{c}, Hj{c}⟩ := low_block_join {stk(-(F + 16 + self.cfr))} {stk(rs)} S {self.cfr} hS (by decide) (by bv_omega)")
                E(f"  lm{c} scr{c} hlm{c} hscr{c} _ _ (by first | ecancel | (dsimp only; ecancel))")
                E(f"clear Hc{c}")
                self.H = f"Hj{c}"
                self.setslot("lo", "SE", ("blk", f"(lm{c} ++ scr{c})", f"hj{c}", seq))
            else:
                self.setslot("lo", "S", ("scrn", f"scr{c}", None, seq))
            self.reg = {"rsp": ("stk", -(F + 8))}
            self.outv[fi] = ("v", fi)
            self.done += 1
            return i + 1
        raise FastPathRefuse(f"directive {i} not in the recipe: {self.L[i]}")

    def frametest(self, i, j, b, rc, rn, vc, vn):
        """`cmp %W,%(ptr - rsp); jb L` in the epilogue: not taken, from the separation of the output and the frame
        (`frame50_pointer_apart`: frame 0x50, >= 64 output bytes, whole 8-byte slots -40, -32, -16, -8)."""
        F = self.F
        if not (F == 80 and vn == ("imm", F + 16) and vc == ("pfr", -(F + 8)) and b[:2] == ("jcc", "jb")
                and self.done == len(self.fields) and self.size >= 64):
            raise FastPathRefuse("frame test form unknown (only the frame 0x50 form with >= 64 output bytes is covered)")
        tgt = self.lab_of(b[2])
        if not any(self.L[x] == "callq runtime.moveSliceNoCapNoScan" for x in range(tgt, min(tgt + 6, len(self.L)))):
            raise FastPathRefuse("frame test branch target is not the moveSlice block")
        ys = []
        for off in (-40, -32, -16, -8):
            v = self.getslot(off, 8)
            ys.append((v_pf(v), v_len(v)))
        ys.append(("(Int.toBytes 8 ra.toBitVec.toInt)", "(Int.toBytes_length 8 _)"))
        if self.emit:
            E = self.E
            nf = len(self.fields)
            names = [self.vn[x] for x in range(nf)]
            cat = "pre ++ " + "".join(f"({n} ++ " for n in names[:-1]) + names[-1] + ")" * (nf - 1)
            ad = lambda o: "(rbx.toBitVec + rcx.toBitVec)" if o == 0 else f"(rbx.toBitVec + rcx.toBitVec + {o})"
            rhs = "Eq (pre.At rbx.toBitVec) ⋆ " + "".join(f"(Eq ({names[x]}.At {ad(self.soff[x])}) ⋆ " for x in range(nf - 1)) \
                + f"Eq ({names[-1]}.At {ad(self.soff[-1])})" + ")" * (nf - 1)
            lens = ", ".join("h" + n for n in names)
            E("have hrdi := rdi.toBitVec.isLt")
            E(f"have hcapn : pre.length + {self.size} ≤ rdi.toBitVec.toNat := by rw [hpre]; exact hcap")
            E(f"have hO : Eq (({cat}).At rbx.toBitVec) = {rhs} := by")
            tails = [("(" + "".join(f"{n} ++ (" for n in names[x:-1]) + names[-1] + ")" * (nf - 1 - x) + ")") if x < nf - 1 else names[-1]
                     for x in range(nf)]
            rw = [f"at_app pre {tails[0]} (b := rbx.toBitVec + rcx.toBitVec)\n      (by rw [hpre]; show _ = _ + BitVec.ofNat 64 rcx.toBitVec.toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])\n"
                  f"      (by simp only [List.length_append, {lens}]; omega)"]
            for x in range(nf - 1):
                rw.append(f"at_app {names[x]} {tails[x + 1]} (b := {ad(self.soff[x + 1])[1:-1]})\n      (by rw [h{names[x]}] <;> bv_omega) "
                          f"(by simp only [List.length_append, {lens}]; omega)")
            E("  rw [" + ",\n    ".join(rw) + "]")
            E("have hfar : 96 ≤ (rbx.toBitVec - (rsp.toBitVec - 88)).toNat :=")
            E(f"  frame50_pointer_apart ({cat}) " + " ".join(y[0] for y in ys) + f" rbx.toBitVec rsp.toBitVec _ {self.mem_}")
            E(f"    (by rw [hO]; ecancel) (by simp only [List.length_append, {lens}]; omega) " + " ".join(y[1] for y in ys))
            _, w = self.win(i, j - i + 1)
            E(f"apply step_cmp_jb_not_taken Reg64.{rc} Reg64.{rn} _ _ {w} _ _ "
              f"(by show (96 : BitVec 64).toNat ≤ (rbx.toBitVec - (rsp.toBitVec - 88)).toNat; exact hfar)")
            E("intro fl; normalize_registers")
        else:
            self.pend = 0
        self.frametested = True
        return j + 1

    # ---------- nested fields ----------
    def nil_test(self, i, j, b, rb, d, ad, fi):
        """`cmpq $0x0,g(%rB); jne l` of the current nested field: taken, from the premise that its pointer is not nil.
        The `newobject` branch between the `jne` and `l` is not on the path."""
        if b[:2] != ("jcc", "jne") or ad != ("rcvw", self.goff[fi]):
            raise FastPathRefuse("nil test is not `cmpq $0x0` of the current nested field word with a `jne`")
        jl = self.lab_of(b[2])
        if jl <= j:
            raise FastPathRefuse("nil test jumps backwards")
        if not any(self.L[x] == "callq runtime.newobject" for x in range(j + 1, jl)):
            raise FastPathRefuse("nil test skips no `newobject` call")
        hl = self.label_hyp(jl)
        a0 = i - self.pend
        self.pend = 0
        g = self.goff[fi]
        self.E(f"apply step_nil_check_taken Reg64.{rb} {lit(d)} _ _ (k + {a0}) (k + {jl}) (window_infix_at hk {a0} {j + 1 - a0}) (by rfl) {hl}")
        self.E(f"  rax.toBitVec (rax.toBitVec + {g}) {self.pn[fi]} (by encoder_address_equation) hp{fi} _ _ _ (by rfl) (by ecancel)")
        self.E("intro fl; normalize_registers")
        self.nilok = fi
        return jl

    def merge_prefix(self, c, fi):
        """`hP{c}`: the prefix and the outputs of the fields before `fi` as one chunk (the prefix of the callee), and its length."""
        names, offs = [], []
        for x in range(fi):
            if self.fields[x][1] == "n":
                names += [self.vn[x], f"rt{x}"]
                offs += [self.soff[x], self.soff[x] + 8]
            else:
                names.append(self.vn[x])
                offs.append(self.soff[x])
        ad = lambda o: "(rbx.toBitVec + rcx.toBitVec)" if o == 0 else f"(rbx.toBitVec + rcx.toBitVec + {o})"
        nn = len(names)
        if nn == 0:
            raise FastPathRefuse("nested field at SSZ offset 0 (no prefix form)")
        cat = "pre ++ " + "".join(f"({n} ++ " for n in names[:-1]) + names[-1] + ")" * (nn - 1)
        rhs = "Eq (pre.At rbx.toBitVec) ⋆ " + "".join(f"(Eq ({names[x]}.At {ad(offs[x])}) ⋆ " for x in range(nn - 1)) \
            + f"Eq ({names[-1]}.At {ad(offs[-1])})" + ")" * (nn - 1)
        lens = ", ".join("h" + n for n in names)
        tails = [("(" + "".join(f"{n} ++ (" for n in names[x:-1]) + names[-1] + ")" * (nn - 1 - x) + ")") if x < nn - 1 else names[-1]
                 for x in range(nn)]
        rw = [f"at_app pre {tails[0]} (b := rbx.toBitVec + rcx.toBitVec)\n      (by rw [hpre]; show _ = _ + BitVec.ofNat 64 rcx.toBitVec.toNat; rw [BitVec.ofNat_toNat, BitVec.setWidth_eq])\n"
              f"      (by simp only [List.length_append, {lens}]; omega)"]
        for x in range(nn - 1):
            rw.append(f"at_app {names[x]} {tails[x + 1]} (b := {ad(offs[x + 1])[1:-1]})\n      (by rw [h{names[x]}] <;> bv_omega) "
                      f"(by simp only [List.length_append, {lens}] <;> omega)")
        self.E("have hrdi := rdi.toBitVec.isLt")
        self.E(f"have hP{c} : Eq (({cat}).At rbx.toBitVec) = {rhs} := by")
        self.E("  rw [" + ",\n    ".join(rw) + "]")
        self.E(f"have hPl{c} : ({cat}).length = (rcx.toBitVec + {self.soff[fi]}).toNat :=")
        self.E(f"  nested_prefix_length rcx rdi {self.soff[fi]} _ (by simp only [List.length_append, hpre, {lens}] <;> omega) (by omega)")
        return f"({cat})"

    def nested_call(self, i):
        """`callq` of the callee of the current nested field (`encode_nested_checkpoint_call`), through the callee function
        specification. The callee frame is the top of the low block: split at the first nested call; the 16-byte
        temp of the callee is joined again from its two words at a later call."""
        F, Ex = self.F, self.cfr
        fi = self.done
        E = self.E
        if fi >= len(self.fields) or self.fields[fi][1] != "n":
            raise FastPathRefuse("call of the nested callee for a field that is not nested")
        if self.nilok != fi:
            raise FastPathRefuse(f"nested call of field {fi} without its nil test")
        if Ex != 120:
            raise FastPathRefuse(f"callee frame {Ex} (covered: 120)")
        vr = (self.reg.get("rax"), self.reg.get("rbx"), self.reg.get("rcx"), self.reg.get("rdi"))
        if vr != (("fptr", self.pn[fi], fi), ("ptr",), ("len", self.soff[fi]), ("cap",)):
            raise FastPathRefuse(f"nested call arguments {vr}")
        rs = -(F + 16)
        if not self.emit:
            self.touch(rs, 8, call=True)
            self.touch(-F, 8)
        if self.pend:
            E(f"apply step_nops _ (k + {i - self.pend}) (k + {i}) (window_infix_at hk {i - self.pend} {self.pend}) (by rfl) (by rfl)")
            self.pend = 0
        self.ncall += 1
        c = self.ncall
        o = lambda n: stk(-(F + n))
        if not self.hcth:
            E(f"have hC : NestedCheckpointCalleeEncode \"{self.callee['label']}\" S := {self.callee['holds']} kC hkC hfC S hmm")
            self.hcth = True
        first = self.slot_at("lo", "SE") is not None
        if first:
            lo = self.getslot("lo", "SE")
            E(f"obtain ⟨sc{c}, rs{c}, gp{c}, ta{c}, tb{c}, la{c}, lb{c}, lc{c}, fq{c}, hsc{c}, hrs{c}, hgp{c}, hta{c}, htb{c}, hla{c}, hlb{c}, "
              f"hlc{c}, hfq{c}, Hs{c}⟩ :=")
            E(f"  low_block_callee_frame_split {o(136)} {o(128)} {o(80)} {o(64)} {o(48)} {o(40)} {o(32)} {o(24)} S hS")
            E("  (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)")
            E(f"  {v_pf(lo)} {v_len(lo)} _ _ (by first | ecancel | (dsimp only; ecancel))")
            E(f"clear {self.H}")
            self.H = f"Hs{c}"
            ins = dict(fp=(f"fq{c}", f"hfq{c}"), l16=(f"lc{c}", f"hlc{c}"), l24=(f"lb{c}", f"hlb{c}"), l32=(f"la{c}", f"hla{c}"),
                       t30=(f"tb{c}", f"htb{c}"), t40=(f"ta{c}", f"hta{c}"), rs=(f"rs{c}", f"hrs{c}"), sc=(f"sc{c}", f"hsc{c}"))
            join = ""
        else:
            g = lambda off, n: self.getslot(-(F + off), n)
            if self.slot_at("lo", "S") is None or self.slot_at(-(F + 128), 48) is None:
                raise FastPathRefuse("internal: callee frame slots of a later nested call")
            ve, vt = g(80, 8), g(72, 8)
            ins = dict(fp=(v_pf(g(24, 8)), v_len(g(24, 8))), l16=(v_pf(g(32, 8)), v_len(g(32, 8))), l24=(v_pf(g(40, 8)), v_len(g(40, 8))),
                       l32=(v_pf(g(48, 8)), v_len(g(48, 8))), t30=(v_pf(g(64, 16)), v_len(g(64, 16))),
                       t40=(f"({v_pf(ve)} ++ {v_pf(vt)})", f"(by rw [List.length_append, {v_len(ve)}, {v_len(vt)}])"),
                       rs=(v_pf(g(136, 8)), v_len(g(136, 8))),
                       sc=(v_pf(self.getslot("lo", "S")), v_len(self.getslot("lo", "S"))))
            join = (f"rw [at_app {v_pf(ve)} {v_pf(vt)} (b := {o(72)[1:-1]}) (by rw [{v_len(ve)}]; bv_omega) "
                    f"(by rw [{v_len(ve)}, {v_len(vt)}]; omega)]; ")
        ret, s2 = self.getslot(rs, 8), self.getslot(-F, 8)
        cat = self.merge_prefix(c, fi)
        so = self.soff[fi]
        ep, rt, p, q = self.vn[fi], f"rt{fi}", self.pn[fi], f"pr{fi}"
        E(f"refine eventually_trans _ _ _ _ (encode_nested_checkpoint_call \"{self.callee['label']}\" S hC (k + {i}) (window_infix_at hk {i} 1)")
        E(f"  {o(8)} {p} {q} rbx.toBitVec (rcx.toBitVec + {so}) rdi.toBitVec (rcx.toBitVec + {so + 40}) (by bv_omega)")
        E(f"  {o(16)} {o(24)} {stk(-F)} {o(32)} {o(40)} {o(48)} {o(64)} {o(80)} {o(72)} {o(136)} ({o(136)[1:-1]} - BitVec.ofNat 64 S)")
        E(f"  {s_pf(('dst', so))} {s_pf(('dst', so + 8))}")
        E("  (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)")
        E("  (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)")
        E(f"  guard (nested_call_stack rsp guard.toNat {F + 8} {self.ga} hguard (by decide)).1 (nested_call_stack rsp guard.toNat {F + 8} {self.ga} hguard (by decide)).2")
        E(f"  (nested_call_capacity rcx rdi {so} (by omega) hcap63) hcap63")
        E(f"  ob{fi} {ep} oc{fi} ot{fi} {rt} {cat} d{fi} dr{fi} {v_pf(ret)} {ins['fp'][0]} {v_pf(s2)} {ins['l16'][0]} {ins['l24'][0]} "
          f"{ins['l32'][0]} {ins['t30'][0]} {ins['t40'][0]} {ins['rs'][0]} {ins['sc'][0]}")
        E(f"  hob{fi} h{ep} hoc{fi} hot{fi} h{rt} hPl{c} hd{fi} hdr{fi} {v_len(ret)} {ins['fp'][1]} {v_len(s2)} {ins['l16'][1]} {ins['l24'][1]} "
          f"{ins['l32'][1]} {ins['t30'][1]} {ins['t40'][1]} {ins['rs'][1]} {ins['sc'][1]}")
        E(f"  _ _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by {join}rw [hP{c}]; first | ecancel | (dsimp only; ecancel))) ?_")
        E(f"clear {self.H}")
        E(f"rintro ⟨e{c}, pc{c}⟩ ⟨hpc{c}, hxa{c}, hxb{c}, hxc{c}, hxd{c}, hxs{c}, hrsp{c}, hrbp{c}, hr14{c}, tt{c}, uu{c}, ss{c}, rr{c}, "
          f"htt{c}, huu{c}, hss{c}, hrr{c}, Hc{c}⟩")
        E(f"dsimp only at hpc{c} hxa{c} hxb{c} hxc{c} hxd{c} hxs{c} hrsp{c} hrbp{c} hr14{c} Hc{c}")
        E(f"subst hpc{c}")
        rn = ", ".join(f"{r}c{c}" for r in R64)
        E(f"obtain ⟨⟨{rn}⟩, zmmsc{c}, flagsc{c}, memc{c}⟩ := e{c}")
        E(f"simp only at hxa{c} hxb{c} hxc{c} hxd{c} hxs{c} hrsp{c} hrbp{c} hr14{c} Hc{c}")
        E(f"subst rspc{c} rbpc{c} r14c{c} rdic{c} rsic{c}")
        E(f"obtain rfl : rbx = raxc{c} := (UInt64.toBitVec_inj.mp hxa{c}).symm")
        E(f"obtain rfl : rdi = rcxc{c} := (UInt64.toBitVec_inj.mp hxc{c}).symm")
        E(f"rw [show k + {i} + 1 = k + {i + 1} from rfl, hP{c}] at Hc{c}")
        E(f"apply register_value_rewrite Reg64.rbx (rcx.toBitVec + {so + 40}) _ _ _ (by exact hxb{c})")
        E("normalize_registers")
        self.H = f"Hc{c}"
        self.mem_ = f"memc{c}"
        self.zm = f"zmmsc{c}"
        # the slots after the call
        newex = lambda: (self.__setattr__("exseq", self.exseq + 1), self.exseq)[1]
        setv = lambda off, n, v: self.setslot(off, n, v) if self.slot_at(off, n) is not None else \
            self.slots.insert(self.slot_at("lo", "SE" if first else "S"), (off, n, v))
        setv(rs, 8, ("ret", i + 1))
        setv(-F, 8, ("reg", "rbx"))
        setv(-(F + 24), 8, ("fpv",))
        setv(-(F + 32), 8, ("reg", "rbx"))
        setv(-(F + 40), 8, ("reg", "rdi"))
        setv(-(F + 48), 8, ("len", so + 40))
        setv(-(F + 64), 16, ("scrn", f"uu{c}", None, newex()))
        if not first:
            j80 = self.slot_at(-(F + 80), 8)
            self.slots[j80:j80 + 2] = [(-(F + 80), 16, None)]
        e16 = self.slot_at(-(F + 80), 16)
        if e16 is None:
            setv(-(F + 80), 16, None)
            e16 = self.slot_at(-(F + 80), 16)
        self.slots[e16:e16 + 1] = [(-(F + 80), 8, ("fld", ep, self.leaf[fi], fi)), (-(F + 72), 8, ("scrn", f"tt{c}", None, newex()))]
        if first:
            setv(-(F + 128), 48, ("scrn", f"gp{c}", None, newex()))
        setv(-(F + 136), 8, ("scrn", f"rr{c}", None, newex()))
        jl = self.slot_at("lo", "SE" if first else "S")
        self.slots[jl] = ("lo", "S", ("scrn", f"ss{c}", None, newex()))
        self.reg = {"rsp": ("stk", -(F + 8)), "rax": ("ptr",), "rbx": ("len", so + 40), "rcx": ("cap",),
                    "rdi": ("imm", 0), "rsi": ("imm", 0)}
        self.callfi = fi
        return i + 1

    def test_branch(self, i, a):
        """`test %rdi,%rdi; je l` after the nested call of the current field: taken (the callee returns a nil error).
        This commits the field; the error wrap between the `je` and `l` is not on the path."""
        j = i + 1
        while self.ins(j)[0] == "nop":
            j += 1
        b = self.ins(j)
        fi = self.done
        if not (self.nested and b[:2] == ("jcc", "je") and a[1] == "rdi" and self.reg.get("rdi") == ("imm", 0)
                and self.callfi == fi):
            raise FastPathRefuse("test form unknown (only `test %rdi,%rdi; je` after a nested call)")
        jl = self.lab_of(b[2])
        if jl <= j:
            raise FastPathRefuse("error test jumps backwards")
        hl = self.label_hyp(jl)
        a0 = i - self.pend
        self.pend = 0
        self.E(f"apply step_test_je_taken Reg64.rdi _ _ (k + {a0}) (k + {jl}) (window_infix_at hk {a0} {j + 1 - a0}) (by rfl) {hl} _ _ (by rfl)")
        self.E("intro fl; normalize_registers")
        self.outv[fi] = ("v", fi)
        self.done += 1
        return jl

    # ---------- boundaries ----------
    def live_after(self, i):
        """registers read before written on the path from directive i (a call or the return ends the scan)"""
        need, written = [], set()
        j, n = i, 0
        prev = None
        while True:
            n += 1
            if n > 2000:
                raise FastPathRefuse("liveness scan does not end")
            a = self.ins(j)
            k = a[0]
            use, df, nxt = [], [], j + 1
            if k == "movrr":
                use, df = [a[2]], [a[1]]
            elif k in ("ld", "lea"):
                use, df = [a[2]], [a[1]]
            elif k == "st":
                use = [a[1], a[2]]
            elif k in ("stidx", "stidx32"):
                use = [a[1], a[2], a[3]]
            elif k == "ld32":
                use, df = [a[2]], [a[1]]
            elif k in ("movi", "xor"):
                df = [a[1]]
            elif k in ("addi", "subi"):
                use, df = [a[1]], [a[1]]
            elif k == "leaidx":
                use, df = [a[2], a[3]], [a[1]]
            elif k in ("addrr", "subrr"):
                use, df = [a[1], a[2]], [a[1]]
            elif k == "cmprr":
                use = [a[1], a[2]]
            elif k in ("cmpmi", "movups"):
                use = [a[1]]
            elif k == "jcc":
                if a[1] == "jae":
                    nxt = self.lab_of(a[2])
                elif self.nested and (a[1] == "je" or (a[1] == "jne" and prev and prev[0] == "cmpmi" and prev[3] == 0)):
                    # the fast path of a nested field: the nil test and the error test are taken
                    nxt = self.lab_of(a[2])
            elif k == "test":
                use = [a[1]]
            elif k == "jmp":
                nxt = self.lab_of(a[1])
            elif k == "call":
                use = ["rax", "rbx", "rcx"] + (["rdi"] if self.nested and a[1] == self.callee["label"] else [])
            elif k == "pop":
                use = ["rax", "rbx", "rcx", "rdi", "rsi"]
            elif k in ("label", "nop"):
                pass
            else:
                raise FastPathRefuse(f"liveness scan: directive {j} `{self.L[j]}` has no use / def rule")
            for r in use:
                if r not in written and r not in need and r not in ("rsp", "rbp", "r14"):
                    need.append(r)
            if k in ("call", "pop"):
                break
            written.update(df)
            if k != "nop":
                prev = a
            j = nxt
        return [r for r in R64 if r in need]

    def boundary(self, pc):
        exs = sorted({(v[3], o) for o, sz, v in self.slots if v[0] in ("ex", "x15", "scrn", "blk")})
        wit, newslots = [], []
        idx = {key: n for n, key in enumerate(exs)}
        for o, sz, v in self.slots:
            if v[0] in ("ex", "x15", "scrn", "blk"):
                n = idx[(v[3], o)]
                wit.append((n, v_pf(v), v_len(v), sz))
                newslots.append((o, sz, ("ex", f"x{n}", n, v[3])))
            else:
                newslots.append((o, sz, v))
        wit.sort()
        regs = [(r, self.reg.get(r)) for r in self.live_after(pc)]
        for r, v in regs:
            if v is None or not (v[0] in ("rcv", "ptr", "cap", "len") or (self.nested and v == ("imm", 0))):
                raise FastPathRefuse(f"live register {r} = {v} at a boundary")
        b = dict(pc=pc, done=self.done, regs=regs, slots=newslots, outv=list(self.outv), exs=[w[3] for w in wit])
        E = self.E
        E("apply Eventually.done")
        parts = ["rfl", "rfl", "rfl", "rfl"] + ["rfl"] * len(regs) + [w[1] for w in wit] + [w[2] for w in wit]
        E("refine ⟨" + ", ".join(parts) + ", ?_⟩")
        E("first | ecancel | (dsimp only; ecancel)")
        self.thms.append(self.out)
        self.out = []
        self.hl = set()
        self.hcth = False
        self.slots = list(newslots)
        self.zm = "zmms1"
        self.H = "Hm"
        self.mem_ = "mem1"
        self.reg = {r: v for r, v in regs}
        self.reg["rsp"] = ("stk", -(self.F + 8))
        return b

    def epilogue(self, i):
        E = self.E
        if (self.reg.get("rax"), self.reg.get("rbx"), self.reg.get("rcx"), self.reg.get("rdi"), self.reg.get("rsi")) != \
                (("ptr",), ("len", self.size), ("cap",), ("imm", 0), ("imm", 0)):
            raise FastPathRefuse(f"result registers at the return: {self.reg}")
        if self.reg.get("rsp") != ("stk", -8):
            raise FastPathRefuse("rsp at the return")
        jr = i + 1
        while self.nested and self.ins(jr) == ("nop",) and jr < i + 4:
            jr += 1
        if self.ins(jr) != ("ret",):
            raise FastPathRefuse("return form (pop %rbp; retq)")
        a0 = i - self.pend
        self.pend = 0
        E(f"refine eventually_trans _ _ _ _ (decode_return_segment _ (k + {a0}) (window_infix_at hk {a0} {jr + 1 - a0}) (by rfl) "
          "(rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) rbp ra _ _ (by rfl) (by ecancel)) ?_")
        E("rintro ⟨d', pc'⟩ ⟨hpc', hrsp', hrbp', hreg', hmem'⟩")
        E("dsimp only at hpc' hrsp' hrbp' hreg' hmem'")
        E("apply Eventually.done")
        exs = [v for o, sz, v in self.slots if v[0] == "ex"]
        exs.sort(key=lambda v: v[2])
        E("refine ⟨hpc', ?_, ?_, ?_, ?_, ?_, ?_, hrbp', ?_, " + ", ".join([v[1] for v in exs] + ["h" + v[1] for v in exs] + ["?_"]) + "⟩")
        g = lambda r: f"exact UInt64.toBitVec_inj.mp (hreg' Reg64.{r} (by decide) (by decide))"
        E("· " + g("rax"))
        E(f"· show d'.regs.rbx.toBitVec.toNat = rcx.toBitVec.toNat + {self.size}")
        E(f"  rw [show d'.regs.rbx.toBitVec = rcx.toBitVec + {self.size} from hreg' Reg64.rbx (by decide) (by decide)]")
        E("  bv_omega")
        E("· " + g("rcx"))
        E("· " + g("rdi"))
        E("· " + g("rsi"))
        E("· rw [hrsp']; apply UInt64.toBitVec_inj.mp")
        E("  first")
        E("    | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)")
        E("    | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)")
        E("· " + g("r14"))
        E("· first | (rw [hmem']; ecancel) | (dsimp only; rw [hmem']; ecancel)")
        self.thms.append(self.out)
        self.final = dict(slots=list(self.slots), exs=[sz for _, sz, _ in sorted(
            [(v[2], sz, v) for o, sz, v in self.slots if v[0] == "ex"], key=lambda x: x[0])])
        self.ended = True

    # ---------- statement text ----------
    def xs(self):
        n = (["ast"] if self.st else []) + [self.vn[i] for i in self.uidx] + [f"c{i}" for i in self.bidx] \
            + [self.vn[i] for i in self.bidx] + ["pre"] + [f"d{i}" for i in range(len(self.fields))]
        ln = [(x, 8) for x in (["ast"] if self.st else []) + [self.vn[i] for i in self.uidx] + [f"c{i}" for i in self.bidx]] \
            + [(self.vn[i], self.fields[i][2]) for i in self.bidx] + [(f"d{i}", f[2]) for i, f in enumerate(self.fields)]
        return n, ln

    def binders(self):
        n, ln = self.xs()
        b = [f"(k : Nat) (hk : {self.C}.IsInfixAt Host.prog k) (hf : LabelsFresh {self.C} k)",
             f"({' '.join(n)} : List UInt8) " + " ".join(f"(h{x} : {x}.length = {l})" for x, l in ln)]
        ps = " ".join(self.pn[i] for i in self.bidx)
        b.append((f"({ps} : BitVec 64) " if ps else "") + "(s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)")
        b.append(f"({' '.join(x[2] for x in self.bind)} : List UInt8) " + " ".join(f"(h{x[2]} : {x[2]}.length = {x[1]})" for x in self.bind))
        b.append("(R : DataMem → Prop)" + (" (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)" if self.rt else ""))
        names = ["k", "hk", "hf"] + n + ["h" + x for x, _ in ln] + ([self.pn[i] for i in self.bidx]) + ["s", "ra", "guard", "hpre"] \
            + [x[2] for x in self.bind] + ["h" + x[2] for x in self.bind] + ["R"] + (["S", "scratch", "hsc"] if self.rt else [])
        return b, names

    def mem(self, slots, outv, ind):
        if self.nested:
            return self.mem_n(slots, outv, ind)
        F = self.F
        c = ["Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)"]
        for o, sz, v in slots:
            ad = f"(s.regs.rsp.toBitVec - {F + 16} - BitVec.ofNat 64 S)" if o == "lo" else stk(o, "s.regs.rsp.toBitVec")
            c.append(f"Eq ({v_pf(v, True)}.At {ad})")
        c.append("Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))")
        rc = lambda g: "s.regs.rax.toBitVec" if g == 0 else f"(s.regs.rax.toBitVec + {g})"
        if self.st:
            c.append("Eq (ast.At s.regs.rax.toBitVec)")
        for i, (nm, k, sz, g) in enumerate(self.fields):
            if k == "u":
                c.append(f"Eq ({self.vn[i]}.At {rc(g)})")
            else:
                c += [f"Eq ((Int.toBytes 8 {self.pn[i]}.toInt).At {rc(g)})", f"Eq ((Int.toBytes 8 {sz}).At {rc(g + 8)})",
                      f"Eq (c{i}.At {rc(g + 16)})"]
        c += [f"Eq ({self.vn[i]}.At {self.pn[i]})" for i in self.bidx]
        c.append("Eq (pre.At s.regs.rbx.toBitVec)")
        for i, ov in enumerate(outv):
            o = self.soff[i]
            ad = "(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)" if o == 0 else f"(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + {o})"
            c.append(f"Eq ({(self.vn[i] if ov[0] == 'v' else 'd' + str(i))}.At {ad})")
        c.append("R")
        return ("\n" + ind + "⋆ ").join(c)

    def stp(self, b, st, ind):
        r = [f"{st}.pc = Host.addrOf (k + {b['pc']})",
             f"{st}.data.regs.rsp = {{ toBitVec := s.regs.rsp.toBitVec - {self.F + 8} }}",
             f"{st}.data.regs.rbp = {{ toBitVec := s.regs.rsp.toBitVec - 8 }}",
             f"{st}.data.regs.r14 = s.regs.r14"]
        r += [f"{st}.data.regs.get64 Reg64.{x} = {s_statement(v)}" for x, v in b["regs"]]
        t = ("\n" + ind + "∧ ").join(r) + " ∧\n" + ind
        t += self.exq(b["exs"])
        return t + "(" + self.mem(b["slots"], b["outv"], ind + "  ") + f") {st}.data.dmem"

    def exq(self, exs):
        if not exs:
            return ""
        return "∃ (" + " ".join(f"x{i}" for i in range(len(exs))) + " : List UInt8), " + \
            " ∧ ".join(f"x{i}.length = {f'S + {self.cfr}' if e == 'SE' else e}" for i, e in enumerate(exs)) + " ∧\n        "

    def finalp(self, ind):
        r = ["st.pc = Int64.ofBitVec ra.toBitVec", "st.data.regs.rax = s.regs.rbx",
             f"st.data.regs.rbx.toNat = s.regs.rcx.toNat + {self.size}", "st.data.regs.rcx = s.regs.rdi",
             "st.data.regs.rdi = 0", "st.data.regs.rsi = 0", "st.data.regs.rsp = s.regs.rsp + 8",
             "st.data.regs.rbp = s.regs.rbp", "st.data.regs.r14 = s.regs.r14"]
        return ("\n" + ind + "∧ ").join(r) + " ∧\n" + ind + self.exq(self.final["exs"]) + \
            "(" + self.mem(self.final["slots"], [("v", i) for i in range(len(self.fields))], ind + "  ") + ") st.data.dmem"

    def prem(self):
        g = "guard.toNat" if self.gd == 0 else f"guard.toNat + {self.gd}"
        return (f"(hguard : {g} < s.regs.rsp.toNat)",
                f"(hsp : {self.F + 16} ≤ s.regs.rsp.toNat)\n    (hcap : s.regs.rcx.toNat + {self.size} ≤ s.regs.rdi.toNat) "
                "(hcap63 : s.regs.rdi.toNat < 2 ^ 63)")

    def slotk(self, slots):
        o = []
        for off, sz, v in slots:
            if off == "lo":
                o.append(f".low ({v_kind(v)})" if v[0] != "scr" else ".low .scratch")
            else:
                o.append(f".at (.{'above' if off > 0 else 'below'} {abs(off)}) ({v_kind(v)})")
        return "[" + ", ".join(o) + "]"

    def exk(self, exs):
        return "[" + ", ".join(".low" if e == "S" else ".lowBlock" if e == "SE" else f".fixed {e}" for e in exs) + "]"

    def layout(self):
        return self.layname or f"Prysm.{self.t}.{self.px}_layout"

    def layout_fields(self):
        pre = self.pre + ([("lo", "S", ("scr",))] if self.rt else [])
        return dict(stateWord=str(self.st).lower(), frame=str(self.F), guardAddend=str(self.gd), callsMemmove=str(self.rt).lower(),
                    stackChunkCount=str(len(self.bind)), stackChunkLengths="[" + ", ".join(f"({i}, {x[1]})" for i, x in enumerate(self.bind)) + "]",
                    pre=self.slotk(pre), existentials=self.exk(self.final["exs"]), post=self.slotk(self.final["slots"]))

    def laydef(self):
        f = self.layout_fields()
        return (f"/-- The frame facts of `{self.C}` (read from the `.S` file by the walk): frame `{self.F:#x}`, stack chunks\n`"
                + " ".join(x[2] for x in self.bind) + f"`. -/\ndef {self.px}_layout : EncoderFrameLayout where\n"
                + "".join(f"  {k} := {f[k]}\n" for k in ("stateWord", "frame", "guardAddend", "callsMemmove", "stackChunkCount", "stackChunkLengths", "pre", "existentials", "post")) + "\n")

    def fieldsk(self):
        return "[" + ", ".join(".uint64" if f[1] == "u" else f".bytes {f[2]}" for f in self.fields) + "]"

    def stk_(self, b):
        regs = "[" + ", ".join(f"(.{r}, {s_kind(v)})" for r, v in b["regs"]) + "]"
        return f"⟨{b['pc']}, {b['done']}, {regs},\n      {self.slotk(b['slots'])},\n      {self.exk(b['exs'])}⟩"

    def text(self):
        """(body text, list of (theorem, kind) emitted)"""
        if self.nested:
            return self.text_n()
        px, C = self.px, self.C
        kinds = []
        bl, names = self.binders()
        B = "\n    ".join(bl)
        hg, hrest = self.prem()
        hmm = " (hmm : MemmoveContract S)" if self.rt else ""
        nm = " ".join(names)
        hmn = " hmm" if self.rt else ""
        ob = "  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s"
        lay, fk = self.layout(), self.fieldsk()
        nf = len(self.fields)
        if len(self.thms) != nf + 2 or len(self.bstate) != nf + 1:
            raise FastPathRefuse(f"internal: {len(self.thms)} proof blocks / {len(self.bstate)} boundaries for {nf} fields")
        o = [self.laydef()] if not self.layname else []
        pre_slots = self.pre + ([("lo", "S", ("scr",))] if self.rt else [])
        hmem = "(h_mem : s.dmem =⋆ " + self.mem(pre_slots, [("d", i) for i in range(nf)], "      ") + ")"
        b0 = self.bstate[0]

        def kline(name, kind, extra):
            kinds.append((name, kind))
            return (f"theorem {name}_kind : ∀ (h : Host), type_of% (@{name} h)\n    = @Codec.{kind} h {C} {lay} {fk}"
                    + extra + " := by\n  intro h; rfl\n")
        o.append(f"{THEOREM_OPTIONS}/-- Head: directives 0–{b0['pc'] - 1} (stack guard, frame, spills); entry → boundary state 0. -/")
        o.append(f"theorem {px}_head : ∀ {B}\n    {hmem}\n    {hg} {hrest}{hmm},\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.stp(b0, "st", "        ") + f")\n      ⟨s, Host.addrOf k⟩ := by")
        o.append(f"  intro {nm} h_mem hguard hsp hcap hcap63{hmn}")
        o.append(ob)
        o.append("  simp only at h_mem hguard hsp hcap hcap63 hpre ⊢")
        o.append(f"  have hcap' : rcx.toBitVec.toNat + {self.size} ≤ rdi.toBitVec.toNat := hcap")
        o += self.thms[0]
        o.append(kline(f"{px}_head", "encodeHeadKindAnyFrame", f"\n    {self.stk_(b0)}"))
        for i in range(nf):
            b, b2 = self.bstate[i], self.bstate[i + 1]
            f = self.fields[i]
            o.append(f"{THEOREM_OPTIONS}/-- Field {i} `{f[0]}` ({'uint64' if f[1] == 'u' else f'{f[2]} bytes'}): directives {b['pc']}–{b2['pc'] - 1}; boundary state {i} → {i + 1}. -/")
            o.append(f"theorem {px}_field_{i} : ∀ {B}\n    {hrest}{hmm} (st0 : MachineState),\n    ("
                     + self.stp(b, "st0", "        ") + ") →\n    Eventually (step1 Host.exe)\n      (fun st => "
                     + self.stp(b2, "st", "        ") + ")\n      st0 := by")
            o.append(f"  intro {nm} hsp hcap hcap63{hmn}")
            o.append(ob)
            o.append("  simp only at hsp hcap hcap63 hpre ⊢")
            o += self.entry(b)
            o += self.thms[i + 1]
            o.append(kline(f"{px}_field_{i}", "encodeFieldKindAnyFrame", f"\n    {self.stk_(b)}\n    {self.stk_(b2)}"))
        b = self.bstate[nf]
        o.append(f"{THEOREM_OPTIONS}/-- Epilogue: directives {b['pc']}–return; boundary state {nf} → the fast-path post-state. -/")
        o.append(f"theorem {px}_epilogue : ∀ {B}\n    {hrest} (st0 : MachineState),\n    ("
                 + self.stp(b, "st0", "        ") + ") →\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.finalp("        ") + ")\n      st0 := by")
        o.append(f"  intro {nm} hsp hcap hcap63")
        o.append(ob)
        o.append("  simp only at hsp hcap hcap63 hpre ⊢")
        o += self.entry(b)
        o += self.thms[nf + 1]
        o.append(kline(f"{px}_epilogue", "encodeEpilogueKindAnyFrame", f"\n    {self.stk_(b)}"))
        o.append(f"{THEOREM_OPTIONS}/-- **Encoder fast path of `(*v1alpha1.{self.t}).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):\n"
                 f"head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + {self.size} ≤ cap`,\n"
                 "every byte-vector field of its exact length. Statement = the kind instance (`_kind`). Fast path only. -/")
        o.append(f"theorem {px}_fast : ∀ {B}\n    {hmem}\n    {hg} {hrest}{hmm},\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.finalp("        ") + ")\n      ⟨s, Host.addrOf k⟩ := by")
        o.append(f"  intro {nm} h_mem hguard hsp hcap hcap63{hmn}")
        o.append(f"  refine eventually_trans _ _ _ _ ({px}_head {nm} h_mem hguard hsp hcap hcap63{hmn}) ?_")
        o.append("  intro st0 h0")
        for i in range(nf):
            o.append(f"  refine eventually_trans _ _ _ _ ({px}_field_{i} {nm} hsp hcap hcap63{hmn} st{i} h{i}) ?_")
            o.append(f"  intro st{i + 1} h{i + 1}")
        o.append(f"  exact {px}_epilogue {nm} hsp hcap hcap63 st{nf} h{nf}")
        o.append(kline(f"{px}_fast", "encodeFastPathKindAnyFrame", ""))
        return "\n".join(o), kinds

    def entry(self, b):
        rf = [f"hr{r}" for r, _ in b["regs"]]
        ex = [f"x{i}" for i in range(len(b["exs"]))]
        o = ["  rintro ⟨d, pc⟩ ⟨" + ", ".join(["hpc", "hrsp", "hrbp", "hr14"] + rf + ex + ["h" + x for x in ex] + ["Hm"]) + "⟩",
             "  dsimp only at hpc hrsp hrbp hr14 " + " ".join(rf) + " Hm",
             "  subst hpc",
             "  obtain ⟨⟨" + ", ".join(r + "1" for r in R64) + "⟩, zmms1, flags1, mem1⟩ := d",
             "  simp only [Reg64s.get64] at hrsp hrbp hr14 " + " ".join(rf) + " Hm",
             "  subst rsp1 rbp1 r141"]
        for r, v in b["regs"]:
            if v == ("imm", 0):
                o.append(f"  obtain rfl : {r}1 = 0 := UInt64.toBitVec_inj.mp hr{r}")
            elif v[0] in ("rcv", "ptr", "cap") or v == ("len", 0):
                e = {"rcv": "rax", "ptr": "rbx", "cap": "rdi", "len": "rcx"}[v[0]]
                o.append(f"  obtain rfl : {e} = {r}1 := (UInt64.toBitVec_inj.mp hr{r}).symm")
            else:
                o.append(f"  obtain rfl : {r}1 = {{ toBitVec := rcx.toBitVec + {v[1]} }} := UInt64.toBitVec_inj.mp hr{r}")
        o.append(f"  have hcap' : rcx.toBitVec.toNat + {self.size} ≤ rdi.toBitVec.toNat := hcap")
        return o

    def imports(self):
        """The modules of the step lemmas beyond FAST_PATH_IMPORTS: the inline-copy steps for a 4-byte field; the nested kinds,
        the nested call block and the callee specification for a nested field."""
        out = list(INLINE_IMPORTS) if any(f[1] == "b" and f[2] == INLINE_SIZE for f in self.fields) else []
        return out + (NESTED_IMPORTS + self.callee["imports"] if self.nested else [])

    def kind_names(self):
        """(head, field, epilogue, fast-path) statement kinds of the form"""
        if self.nested:
            return ("encodeHeadNestedKindAnyFrame", "encodeFieldNestedKindAnyFrame", "encodeEpilogueNestedKindAnyFrame",
                    "encodeFastPathNestedKindAnyFrame")
        return ("encodeHeadKindAnyFrame", "encodeFieldKindAnyFrame", "encodeEpilogueKindAnyFrame", "encodeFastPathKindAnyFrame")

    # ---------- statement text, nested fields (the kinds of `Codec/Kind/EncodeFastPathNestedAnyFrame.lean`) ----------
    def xs_n(self):
        lv, ob, ou = [], [], []
        for i, f in enumerate(self.fields):
            if f[1] == "n":
                lv += [(self.vn[i], 8), (f"rt{i}", 32)]
                ob += [(f"ob{i}", 8), (f"oc{i}", 8), (f"ot{i}", 32)]
                ou += [(f"d{i}", 8), (f"dr{i}", 32)]
            else:
                lv.append((self.vn[i], f[2]))
                ou.append((f"d{i}", f[2]))
        n = [x for x, _ in lv + ob] + ["pre"] + [x for x, _ in ou]
        return n, lv + ob + ou

    def binders_n(self):
        n, ln = self.xs_n()
        code = self.callee["code"]
        ps = [x for i in self.bidx + self.nidx for x in ([self.pn[i]] if self.fields[i][1] == "b" else [self.pn[i], f"pr{i}"])]
        ps = [x for i in range(len(self.fields)) for x in
              ([self.pn[i]] if self.fields[i][1] == "b" else [self.pn[i], f"pr{i}"] if self.fields[i][1] == "n" else [])]
        nn = [f"(hp{i} : {self.pn[i]} ≠ 0)" for i in self.nidx]
        b = [f"(k : Nat) (hk : {self.C}.IsInfixAt Host.prog k) (hf : LabelsFresh {self.C} k)",
             f"(kC : Nat) (hkC : {code}.IsInfixAt Host.prog kC) (hfC : LabelsFresh {code} kC)",
             f"({' '.join(n)} : List UInt8) " + " ".join(f"(h{x} : {x}.length = {l})" for x, l in ln),
             f"({' '.join(ps)} : BitVec 64) " + " ".join(nn) + " (s : MachineData) (ra guard : UInt64) (hpre : pre.length = s.regs.rcx.toNat)",
             f"({' '.join(x[2] for x in self.bind)} : List UInt8) " + " ".join(f"(h{x[2]} : {x[2]}.length = {x[1]})" for x in self.bind),
             f"(R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S + {self.cfr})"]
        names = ["k", "hk", "hf", "kC", "hkC", "hfC"] + n + ["h" + x for x, _ in ln] + ps + [f"hp{i}" for i in self.nidx] \
            + ["s", "ra", "guard", "hpre"] + [x[2] for x in self.bind] + ["h" + x[2] for x in self.bind] + ["R", "S", "hS", "scratch", "hsc"]
        return b, names

    def mem_n(self, slots, outv, ind):
        F = self.F
        c = ["Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)"]
        for o, sz, v in slots:
            ad = f"(s.regs.rsp.toBitVec - {F + 16 + self.cfr} - BitVec.ofNat 64 S)" if o == "lo" else stk(o, "s.regs.rsp.toBitVec")
            c.append(f"Eq ({v_pf(v, True)}.At {ad})")
        c.append("Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))")
        rc = lambda g: "s.regs.rax.toBitVec" if g == 0 else f"(s.regs.rax.toBitVec + {g})"
        for i, f in enumerate(self.fields):
            g = self.goff[i]
            if f[1] == "u":
                c.append(f"Eq ({self.vn[i]}.At {rc(g)})")
            elif f[1] == "b":
                c += [f"Eq ((Int.toBytes 8 {self.pn[i]}.toInt).At {rc(g)})", f"Eq ((Int.toBytes 8 {f[2]}).At {rc(g + 8)})"]
            else:
                c.append(f"Eq ((Int.toBytes 8 {self.pn[i]}.toInt).At {rc(g)})")
        for i, f in enumerate(self.fields):
            p = self.pn.get(i)
            if f[1] == "b":
                c.append(f"Eq ({self.vn[i]}.At {p})")
            elif f[1] == "n":
                c += [f"Eq (ob{i}.At {p})", f"Eq ({self.vn[i]}.At ({p} + 8))", f"Eq ((Int.toBytes 8 pr{i}.toInt).At ({p} + 16))",
                      f"Eq ((Int.toBytes 8 32).At ({p} + 24))", f"Eq (oc{i}.At ({p} + 32))", f"Eq (ot{i}.At ({p} + 40))",
                      f"Eq (rt{i}.At pr{i})"]
        c.append("Eq (pre.At s.regs.rbx.toBitVec)")
        ad = lambda o: "(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)" if o == 0 else f"(s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + {o})"
        for i, ov in enumerate(outv):
            o = self.soff[i]
            if self.fields[i][1] == "n":
                a, b = (self.vn[i], f"rt{i}") if ov[0] == "v" else (f"d{i}", f"dr{i}")
                c += [f"Eq ({a}.At {ad(o)})", f"Eq ({b}.At {ad(o + 8)})"]
            else:
                c.append(f"Eq ({(self.vn[i] if ov[0] == 'v' else 'd' + str(i))}.At {ad(o)})")
        c.append("R")
        return ("\n" + ind + "⋆ ").join(c)

    def layout_fields_n(self):
        pre = self.pre + [("lo", "SE", ("scr",))]
        return dict(callees=f"[{self.callee['code']}]", goStart=str(self.goff[0]), frame=str(self.F), guardAddend=str(self.ga),
                    lowExtra=str(self.cfr), stackChunkCount=str(len(self.bind)),
                    stackChunkLengths="[" + ", ".join(f"({i}, {x[1]})" for i, x in enumerate(self.bind)) + "]",
                    pre=self.slotk(pre), existentials=self.exk(self.final["exs"]), post=self.slotk(self.final["slots"]))

    def text_n(self):
        """(body text, list of (theorem, kind) emitted) of a file with nested fields"""
        px, C = self.px, self.C
        kinds = []
        bl, names = self.binders_n()
        B = "\n    ".join(bl)
        hg = f"(hguard : guard.toNat + {self.ga} < s.regs.rsp.toNat)"
        hrest = f"(hcap : s.regs.rcx.toNat + {self.size} ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)"
        nm = " ".join(names)
        ob = "  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s"
        lay = self.layout()
        fk = "[" + ", ".join(".flat .uint64" if f[1] == "u" else f".flat (.bytes {f[2]})" if f[1] == "b" else ".checkpoint"
                             for f in self.fields) + "]"
        KH, KF, KE, KP = self.kind_names()
        nf = len(self.fields)
        if len(self.thms) != nf + 2 or len(self.bstate) != nf + 1:
            raise FastPathRefuse(f"internal: {len(self.thms)} proof blocks / {len(self.bstate)} boundaries for {nf} fields")
        f = self.layout_fields_n()
        o = [(f"/-- The frame facts of `{self.C}` (read from the `.S` file by the walk): frame `{self.F:#x}`, stack chunks\n`"
              + " ".join(x[2] for x in self.bind) + f"`, the callee `{self.callee['code']}`. -/\n"
              f"def {px}_layout : EncoderNestedFrameLayout where\n"
              + "".join(f"  {k} := {f[k]}\n" for k in NESTED_LAYOUT_FIELDS) + "\n")]
        hmem = "(h_mem : s.dmem =⋆ " + self.mem(self.pre + [("lo", "SE", ("scr",))], [("d", i) for i in range(nf)], "      ") + ")"
        b0 = self.bstate[0]

        def kline(name, kind, extra):
            kinds.append((name, kind))
            return (f"theorem {name}_kind : ∀ (h : Host), type_of% (@{name} h)\n    = @Codec.{kind} h {C} {lay} {fk}"
                    + extra + " := by\n  intro h; rfl\n")
        what = lambda f: "uint64" if f[1] == "u" else f"{f[2]} bytes" if f[1] == "b" else f"nested {f[4]}"
        o.append(f"{NESTED_THEOREM_OPTIONS['head']}/-- Head: directives 0–{b0['pc'] - 1} (stack guard, frame, spills); entry → boundary state 0. -/")
        o.append(f"theorem {px}_head : ∀ {B}\n    {hmem}\n    {hg} {hrest} (hmm : MemmoveContract S),\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.stp(b0, "st", "        ") + f")\n      ⟨s, Host.addrOf k⟩ := by")
        o.append(f"  intro {nm} h_mem hguard hcap hcap63 hmm")
        o.append(ob)
        o.append("  simp only at h_mem hguard hcap hcap63 hpre ⊢")
        o.append(f"  have hcap' : rcx.toBitVec.toNat + {self.size} ≤ rdi.toBitVec.toNat := hcap")
        o += self.thms[0]
        o.append(kline(f"{px}_head", KH, f"\n    {self.stk_(b0)}"))
        for i in range(nf):
            b, b2 = self.bstate[i], self.bstate[i + 1]
            fl = self.fields[i]
            opt = NESTED_THEOREM_OPTIONS["nested" if fl[1] == "n" else "field"]
            o.append(f"{opt}/-- Field {i} `{fl[0]}` ({what(fl)}): directives {b['pc']}–{b2['pc'] - 1}; boundary state {i} → {i + 1}. -/")
            o.append(f"theorem {px}_field_{i} : ∀ {B}\n    {hg} {hrest} (hmm : MemmoveContract S) (st0 : MachineState),\n    ("
                     + self.stp(b, "st0", "        ") + ") →\n    Eventually (step1 Host.exe)\n      (fun st => "
                     + self.stp(b2, "st", "        ") + ")\n      st0 := by")
            o.append(f"  intro {nm} hguard hcap hcap63 hmm")
            o.append(ob)
            o.append("  simp only at hguard hcap hcap63 hpre ⊢")
            o += self.entry(b)
            o += self.thms[i + 1]
            o.append(kline(f"{px}_field_{i}", KF, f"\n    {self.stk_(b)}\n    {self.stk_(b2)}"))
        b = self.bstate[nf]
        o.append(f"{NESTED_THEOREM_OPTIONS['epilogue']}/-- Epilogue: directives {b['pc']}–return; boundary state {nf} → the fast-path post-state. -/")
        o.append(f"theorem {px}_epilogue : ∀ {B}\n    {hg} {hrest} (st0 : MachineState),\n    ("
                 + self.stp(b, "st0", "        ") + ") →\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.finalp("        ") + ")\n      st0 := by")
        o.append(f"  intro {nm} hguard hcap hcap63")
        o.append(ob)
        o.append("  simp only at hguard hcap hcap63 hpre ⊢")
        o += self.entry(b)
        o += self.thms[nf + 1]
        o.append(kline(f"{px}_epilogue", KE, f"\n    {self.stk_(b)}"))
        o.append(f"{NESTED_THEOREM_OPTIONS['fast']}/-- **Encoder fast path of `(*v1alpha1.{self.t}).MarshalSSZTo` (Go 1.26.10), generated** (`encoder --fast-path`):\n"
                 f"head, one theorem per field, epilogue, chained by `eventually_trans`. Premises: `len + {self.size} ≤ cap`,\n"
                 "every byte-vector field of its exact length, every nested pointer not nil, the callee placed.\n"
                 "Statement = the kind instance (`_kind`). Fast path only. -/")
        o.append(f"theorem {px}_fast : ∀ {B}\n    {hmem}\n    {hg} {hrest} (hmm : MemmoveContract S),\n    Eventually (step1 Host.exe)\n      (fun st => "
                 + self.finalp("        ") + ")\n      ⟨s, Host.addrOf k⟩ := by")
        o.append(f"  intro {nm} h_mem hguard hcap hcap63 hmm")
        o.append(f"  refine eventually_trans _ _ _ _ ({px}_head {nm} h_mem hguard hcap hcap63 hmm) ?_")
        o.append("  intro st0 h0")
        for i in range(nf):
            o.append(f"  refine eventually_trans _ _ _ _ ({px}_field_{i} {nm} hguard hcap hcap63 hmm st{i} h{i}) ?_")
            o.append(f"  intro st{i + 1} h{i + 1}")
        o.append(f"  exact {px}_epilogue {nm} hguard hcap hcap63 st{nf} h{nf}")
        o.append(kline(f"{px}_fast", KP, ""))
        return "\n".join(o), kinds

    def meta(self):
        """facts for the FAST-PATH-JSON header (kindcheck recomputes them independently; they are not trusted)"""
        return dict(type=self.t, const=self.C, prefix=self.px, size=self.size, frame=self.F, guard_addend=self.gd, runtime_calls=self.rt,
                    fields=[[f[0], f[1], f[2]] for f in self.fields], boundaries=[b["pc"] for b in self.bstate],
                    layout=self.layout(), assembly_sha256=self.Ssha, ir_sha256=self.irsha)
