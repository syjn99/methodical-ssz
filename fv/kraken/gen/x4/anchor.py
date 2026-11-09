"""Anchored hand templates for fixed containers with byte-vector and container fields (X4: reduced
Checkpoint/AttestationData; X5: the same templates against other code).

This is the weakest generation mode of gen/x4 (weaker than lcacc.py and like lcmarsh.py, but with no
hand-made template file): the template is read from the hand Lean modules at generation time.
- The hand theorem and every hand declaration it uses from the type's own hand modules (closure by name)
  are copied. Statements become `def <obl>_stmt [Host] : Prop := ∀ <binders>, <type>`; proofs are the hand
  tactic text after `intro <binder names>`.
- What the code decides: the position of every label of the target function, and from it every directive
  number in the text (`kat hk C N`, `klabel hk hf C N`, `k + N`, `isInfixAt_drop hk N`): N in the hand code
  is (label j, offset o); in the target it is label j of the target plus o. The rip-relative symbol operands
  (`type__+N`, `ssz.ErrSize`) are paired by position and substituted in the text (`label "s" + N`).
- What it checks: the whole target function, normalised (own label names -> label ordinal, symbol
  operands -> ordinal of first use), must equal the normalised hand function; otherwise the template is
  refused with the first differing directive. So the template applies only to code that equals the hand
  case up to label placement and symbol addresses. The Desc gates the template (anchor_desc_gate).
Nothing else is decided from the code. Python 3 standard library only.
"""
import os
import re

DECL = re.compile(r"^(?:private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|instance)\s+([^\s(:{\[]+)")
PREFIX = re.compile(r"^(set_option \S+ \S+ in|open [^\n]* in|@\[.*\]|/--.*)")


def decls(path):
    """Top-level declarations of a Lean file: name -> (kind, text, file opens). A declaration starts at a
    column-0 `theorem|def|...` line with its attached `set_option .. in`, `open .. in`, docstring and
    attribute lines; it ends before the next non-empty column-0 line."""
    lines = open(path).read().split("\n")
    out, order, opens, i = {}, [], [], 0
    pend = []
    in_doc = False
    while i < len(lines):
        l = lines[i]
        if in_doc:
            pend.append(l)
            in_doc = "-/" not in l
            i += 1
            continue
        if l.startswith("open ") and not l.rstrip().endswith(" in"):
            opens += l.split()[1:]
            i += 1
            continue
        if PREFIX.match(l):
            pend.append(l)
            in_doc = l.startswith("/--") and "-/" not in l
            i += 1
            continue
        m = DECL.match(l)
        if m:
            body = [l]
            j = i + 1
            while j < len(lines) and (not lines[j] or lines[j][0] == " "):
                body.append(lines[j])
                j += 1
            while body and not body[-1].strip():
                body.pop()
            out[m[2]] = (m[1], "\n".join(pend + body), list(opens))
            order.append(m[2])
            pend = []
            i = j
            continue
        pend = []
        i += 1
    return out, order


def imports(path):
    return [l.split()[1] for l in open(path) if l.startswith("import ")]


IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")


def closure(roots, own):
    """Names of the own hand modules that the roots use, transitively (by identifier text)."""
    need, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in need:
            continue
        need.add(n)
        for w in set(IDENT.findall(own[n][1])):
            for c in (w, w.split(".")[-1]):
                if c in own and c not in need and c != n:
                    todo.append(c)
    return need


# ---------------------------------------------------------------- code normalisation and anchors

SYM = re.compile(r"([A-Za-z_][\w.]*?)(\+(\d+))?\(%rip\)")


def directives(path):
    out = []
    for line in open(path):
        t = line.strip()
        if t:
            out.append(("label" if t.endswith(":") else "instr", t.rstrip(":")))
    return out


def normalise(D):
    """(normalised texts, label positions, symbol list in order of first use)."""
    labs = [i for i, (k, _) in enumerate(D) if k == "label"]
    lname = {t: n for n, (i, (k, t)) in enumerate([(i, D[i]) for i in labs])}
    syms, norm = [], []
    for k, t in D:
        if k == "label":
            norm.append(f"LABEL#{lname[t]}")
            continue
        def sym(m):
            s = (m[1], int(m[3] or 0))
            if s not in syms:
                syms.append(s)
            return f"SYM#{syms.index(s)}(%rip)"
        x = SYM.sub(sym, t)
        x = re.sub(r"\b(L_\S+)", lambda m: f"LABEL#{lname[m[1] + ''] }" if m[1] in lname else m[1], x)
        norm.append(x)
    return norm, labs, syms


class Anchor:
    """Map hand directive numbers to target directive numbers; refuse unless the code is equal."""

    def __init__(self, hand_S, target_S):
        self.hand, self.target = hand_S, target_S
        nh, self.lh, self.sh = normalise(directives(hand_S))
        nt, self.lt, self.st = normalise(directives(target_S))
        if len(nh) != len(nt) or len(self.lh) != len(self.lt):
            raise ValueError(f"{os.path.basename(target_S)}: {len(nt)} directives / {len(self.lt)} labels, "
                             f"the hand template has {len(nh)} / {len(self.lh)}")
        for i, (a, b) in enumerate(zip(nh, nt)):
            if i and a != b:   # directive 0 is the function name
                raise ValueError(f"{os.path.basename(target_S)}: directive {i} is `{b}`, the hand template needs `{a}`")
        self.symmap = {a: b for a, b in zip(self.sh, self.st) if a != b}

    def num(self, n):
        j = max(x for x in range(len(self.lh)) if self.lh[x] <= n)
        return self.lt[j] + (n - self.lh[j])


def lean_sym(s):
    return f'label "{s[0]}"' + (f" + {s[1]}" if s[1] else "")


def retarget(text, hand_code, new_code, A):
    """Directive numbers through the anchor, symbols through the pairing, the code name renamed."""
    c = re.escape(hand_code)
    text = re.sub(rf"(kat hk {c} )(\d+)", lambda m: m[1] + str(A.num(int(m[2]))), text)
    text = re.sub(rf"(klabel hk hf {c} )(\d+)", lambda m: m[1] + str(A.num(int(m[2]))), text)
    text = re.sub(r"(isInfixAt_drop hk )(\d+)", lambda m: m[1] + str(A.num(int(m[2]))), text)
    text = re.sub(r"(\bk \+ )(\d+)", lambda m: m[1] + str(A.num(int(m[2]))), text)
    for a, b in A.symmap.items():
        if a[1] == 0 or b[1] == 0:
            raise ValueError(f"symbol {a} -> {b}: a zero offset cannot be retargeted in the text")
        text = re.sub(re.escape(lean_sym(a)) + r"(?!\d)", lean_sym(b), text)
    return re.sub(rf"\b{c}\b", new_code, text)


# ---------------------------------------------------------------- statements

def split_theorem(text, name):
    """(prefix lines, binders, type, proof) of `theorem name binders : type := by proof`."""
    lines = text.split("\n")
    k = next(i for i, l in enumerate(lines) if DECL.match(l))
    pre, src = lines[:k], "\n".join(lines[k:])
    i = src.index(name) + len(name)
    depth, colon, by = 0, None, None
    j = i
    while j < len(src):
        ch = src[j]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and src.startswith(":= by", j):
            by = j
            break
        elif depth == 0 and ch == ":" and colon is None and src[j + 1] in " \n":
            colon = j
        j += 1
    binders, typ, proof = src[i:colon].strip(), src[colon + 1:by].strip(), src[by + len(":= by"):]
    return pre, binders, typ, proof.lstrip("\n")


def binder_names(binders):
    names, depth, cur = [], 0, ""
    for ch in binders:
        if ch in "([{⟨":
            depth += 1
            if depth == 1:
                cur = ""
                continue
        elif ch in ")]}⟩":
            depth -= 1
            if depth == 0:
                head = cur.split(" : ")[0] if " : " in cur else cur.split(":")[0]
                names += head.split()
                continue
        if depth >= 1:
            cur += ch
    return names


def stmt_and_theorem(text, hand_name, obl):
    pre, binders, typ, proof = split_theorem(text, hand_name)
    opts = [p for p in pre if p.startswith("set_option ")]
    ins = [p for p in pre if p.startswith("open ")]
    stmt = ins + [f"def {obl}_stmt [Host] : Prop :=", f"  ∀ {binders},", f"    {typ}", ""]
    thm = ins + opts + [f"theorem {obl} [Host] : {obl}_stmt := by", f"  intro {' '.join(binder_names(binders))}",
                        proof.rstrip(), ""]
    return stmt, thm


# ---------------------------------------------------------------- module

def build(rows, own_files, code_of, ns, header):
    """rows: [(obligation, hand theorem, hand code, new code, hand .S, target .S)].
    own_files: hand modules whose declarations are copied (never imported). code_of: hand code -> (hand .S,
    target .S, new code) for helper declarations that walk code. Returns (module text, report)."""
    own, order, imps = {}, [], []
    for f in own_files:
        d, o = decls(f)
        own.update(d)
        order += o
        imps += [i for i in imports(f) if i not in imps]
    mods = {"Fk." + os.path.splitext(os.path.basename(f))[0] for f in own_files}
    imps = [i for i in imps if i not in mods]
    mains = {r[1]: r[0] for r in rows}
    need = closure(list(mains), own)
    helpers = [n for n in order if n in need and n not in mains]
    anchors = {}

    def anchor(code):
        if code not in anchors:
            hs, ts, _ = code_of[code]
            anchors[code] = Anchor(hs, ts)
        return anchors[code]

    def fix(text):
        for hc in code_of:
            if re.search(rf"\b{re.escape(hc)}\b", text):
                text = retarget(text, hc, code_of[hc][2], anchor(hc))
        for h, o in mains.items():
            text = re.sub(rf"\b{re.escape(h)}\b", o, text)
        return text

    out = [*header, *[f"import {i}" for i in imps], "", f"namespace {ns}", "open Fk Fk.Code", ""]
    if helpers:
        out += ["section", "variable [Host]", "-- hand declarations used by the theorems below (copied, retargeted)"]
        for n in helpers:
            kind, text, opens = own[n]
            extra = [o for o in opens if o not in ("Fk", "Fk.Code")]
            out += ([f"open {' '.join(extra)} in"] if extra and kind != "structure" else []) + [fix(text), ""]
        out += ["end", ""]
    for obl, hname, *_ in rows:
        kind, text, opens = own[hname]
        extra = [o for o in opens if o not in ("Fk", "Fk.Code")]
        stmt, thm = stmt_and_theorem(fix(text), mains[hname], obl)
        op = [f"open {' '.join(extra)} in"] if extra else []
        out += [f"-- {obl}: hand text of {hname}, retargeted (anchor.py)"] + op + stmt + op + thm
    out += [f"end {ns}", ""]
    rep = {"helpers_copied": helpers, "imports": imps,
           "anchors": {c: {"labels": len(a.lt), "symbols_changed": sorted(map(str, a.symmap.items()))}
                       for c, a in anchors.items()}}
    return "\n".join(out), rep


# ---------------------------------------------------------------- Desc gate

def leaves(fields):
    """(kind, length) of every leaf of an SSZ container term, depth first."""
    for f in fields:
        if f["k"] == "container":
            yield ("container", None)
            yield from leaves(f["fields"])
        else:
            yield (f["k"], f.get("n", f.get("w")))


def basic_gate(desc, Dsz, Dun):
    """Gate of the hand-case templates of gen/x4 types: a fixed type has SizeSSZ = `mov $fixed_size,%eax; retq`
    and the decoder's length check `cmp $fixed_size,%rcx`; a variable type's first `cmp $imm,%rcx` of the
    decoder is its fixed part size. Raises ValueError otherwise."""
    fs, fp = desc["fixed_size"], desc["fixed_part_size"]
    un = [t for k, t in Dun if k == "instr"]
    cmp = [t for t in un if re.fullmatch(r"cmp \$0x[0-9a-f]+,%rcx", t)]
    if fs is not None:
        sz = [t for k, t in Dsz if k == "instr"]
        if sz != [f"mov ${hex(fs)},%eax", "retq"]:
            raise ValueError(f"SizeSSZ is {sz}, not `mov ${hex(fs)},%eax; retq`")
    if not cmp or cmp[0] != f"cmp ${hex(fp)},%rcx":
        raise ValueError(f"decoder's first length check {cmp[:1]} is not cmp ${hex(fp)},%rcx (fixed part {fp})")
    return {"fixed_size": fs, "fixed_part_size": fp}


def desc_gate(desc, Dsz, Dun, Dma):
    """The Desc decides which template may be used: fixed size (SizeSSZ immediate, decoder length check),
    one makeslice of the byte-vector length per byte vector (in order), one newobject per container field,
    one memmove per byte vector in the encoder. Raises ValueError otherwise."""
    fs = desc["fixed_size"]
    if desc.get("variable_order") or fs != desc.get("fixed_part_size"):
        raise ValueError("not a fixed-size container")
    sz = [t for k, t in Dsz if k == "instr"]
    if sz != [f"mov ${hex(fs)},%eax", "retq"]:
        raise ValueError(f"SizeSSZ is {sz}, not `mov ${hex(fs)},%eax; retq`")
    un = [t for k, t in Dun if k == "instr"]
    cmp = [t for t in un if re.fullmatch(r"cmp \$0x[0-9a-f]+,%rcx", t)]
    if not cmp or cmp[0] != f"cmp ${hex(fs)},%rcx":
        raise ValueError(f"decoder length check {cmp[:1]} is not cmp ${hex(fs)},%rcx")
    lv = list(leaves(desc["ssz"]["fields"]))
    bv = [n for k, n in lv if k == "byteVector"]
    if any(k not in ("uint", "byteVector", "container") for k, _ in lv):
        raise ValueError(f"field kinds {sorted({k for k, _ in lv})}: the template takes uint, byteVector, container")
    ms = [i for i, t in enumerate(un) if t == "callq runtime.makeslice"]
    if len(ms) != len(bv):
        raise ValueError(f"{len(ms)} makeslice calls, the Desc has {len(bv)} byte vectors")
    for i, n in zip(ms, bv):
        if f"mov ${hex(n)},%ecx" not in un[max(0, i - 3):i]:
            raise ValueError(f"makeslice at instruction {i} does not take the byte-vector length {n}")
    nc = sum(k == "container" for k, _ in lv)
    if un.count("callq runtime.newobject") != nc:
        raise ValueError(f"{un.count('callq runtime.newobject')} newobject calls, the Desc has {nc} container fields")
    mm = [t for k, t in Dma if k == "instr"].count("callq runtime.memmove")
    if mm != len(bv):
        raise ValueError(f"{mm} memmove calls in the encoder, the Desc has {len(bv)} byte vectors")
    return {"fixed_size": fs, "byte_vectors": bv, "containers": nc}
