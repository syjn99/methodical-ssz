#!/usr/bin/env python3
"""ENC2 preparation (unit E2-P): survey of the MarshalSSZTo `.S` of the 16 flat development types.

Usage (Python 3 standard library only; python3 -I -B; reads committed `.S` files only, no ELF, no tool):
  enc2survey.py <out.md>      run from fv/kraken; writes the survey (prysm/go1.26.10/e2e/scal/enc2-survey.md)

Line numbers are 1-based lines of the `.S` file (line 1 = the function label). Field blocks are found by the
growslice sites: every field has exactly one `callq runtime.growslice` (asserted against the IR field count).
A field block runs from the line after the previous field's commit (or after the prologue spills) to its own
commit: the `callq runtime.memmove` (byte vector) or the store into the dst backing array (`mov %r,d(%a,%b,1)`).
The script reports directives and branch targets; it does not prove anything and does not decide reachability
beyond quoting the branch directives.
"""
import json
import pathlib
import re
import sys

ROOT = pathlib.Path("prysm/go1.26.10/e2e")
V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
# (type, link dir); the fields come from prysm/ir/ir-mainnet.json (v1alpha1 package, exported Go fields in order)
TYPES = [("Checkpoint", "link"), ("BeaconBlockHeader", "bh/link"), ("Eth1Data", "e1/link")] + [
    (t, "enc2/link") for t in ("BlobIdentifier", "DepositMessage", "Deposit_Data", "PendingPartialWithdrawal",
                               "SyncCommitteeMessage", "PendingConsolidation", "PendingDeposit", "PowBlock",
                               "HistoricalSummary", "SigningData", "SyncAggregatorSelectionData",
                               "ValidatorBalance", "VoluntaryExit")]
PKG = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"


def ir_fields(t):
    """(name, kind, size, go offset, go type) per exported field: kind b (ssz-size tag) or u64 (8-byte scalar)."""
    d = json.load(open("prysm/ir/ir-mainnet.json"))
    ty = [x for c in d["configs"] if c["package"] == PKG for x in c["types"] if x["name"] == t]
    assert len(ty) == 1, (t, len(ty))
    out = []
    for f in ty[0]["go_fields"]:
        if not f["exported"]:
            continue
        m = re.search(r'ssz-size:"(\d+)"', f["tag"])
        if m:
            out.append((f["name"], "b", int(m[1]), f["offset_gc_amd64"], "[]byte"))
        else:
            assert f["size_gc_amd64"] == 8, (t, f["name"])
            out.append((f["name"], "u64", 8, f["offset_gc_amd64"], f["type"].split("/")[-1]))
    return out


STORE = re.compile(r"mov %(\w+),(-?0x[0-9a-f]+)?\(%(\w+),%(\w+),1\)")
MNEM = re.compile(r"(\S+)")


def short(l, fn):
    return l.replace(f"L_{fn}_", "L_")


def load(t, d):
    fn = f"{V}.{t}.MarshalSSZTo"
    p = ROOT / d / "norm" / f"{fn}.S"
    lines = p.read_text().split("\n")
    return fn, p, [short(l.strip(), fn) for l in lines]


def labels(L):
    return {l[:-1]: i + 1 for i, l in enumerate(L) if l.startswith("L_") and l.endswith(":")}


def target(l):
    m = re.search(r"(L_[0-9a-f]+)$", l)
    return m[1] if m else None


def survey(t, d):
    fields = ir_fields(t)
    fn, p, L = load(t, d)
    lab = labels(L)
    n = lambda i: i + 1  # noqa: E731  (0-based index -> .S line)
    out = [f"### {t}", "", f"File: `{p}` ({len(L) - (1 if L[-1] == '' else 0)} lines)."]
    sub = L.index("mov %rsp,%rbp") + 1
    fm = re.fullmatch(r"(sub \$0x|add \$-0x)([0-9a-f]+),%rsp", L[sub])
    assert fm, (t, L[sub])
    frame = int(fm[2], 16)
    jb0 = next(i for i in range(sub) if L[i].startswith("jbe "))
    guard = [i for i in range(jb0 + 1) if L[i] and not L[i].endswith(":")]
    large = L[guard[0]].startswith("lea -")
    ms = next(i for i, l in enumerate(L) if l == "callq runtime.morestack_noctxt.abi0")
    spills, j = [], sub + 1
    while re.fullmatch(r"mov %\w+,0x[0-9a-f]+\(%rsp\)", L[j]):
        spills.append(j)
        j += 1
    gs = [i for i, l in enumerate(L) if l == "callq runtime.growslice"]
    assert len(gs) == len(fields), (t, len(gs), len(fields))
    out.append(f"Frame: `{L[sub]}` (line {n(sub)}) = {frame} bytes; prologue "
               f"{'large-frame guard' if large else 'small guard'}: "
               + "; ".join(f"`{L[i]}` ({n(i)})" for i in guard)
               + "; then " + "; ".join(f"`{L[i]}` ({n(i)})" for i in range(jb0 + 1, sub + 1))
               + f"; morestack block label line {lab[target(L[jb0])]}, "
               f"call line {n(ms)}.")
    out.append("Spills after `sub`: " + ("; ".join(f"`{L[i]}` ({n(i)})" for i in spills) or "none") + ".")
    out.append("")
    out.append("| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) "
               "| growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |")
    out.append("| - | - | - | - | - | - | - | - | - | - | - |")
    start = (spills[-1] if spills else sub) + 1
    forms = []
    for k, ((name, kind, size, goff, gty), g) in enumerate(zip(fields, gs)):
        # commit = first memmove (bytes) or first store into dst backing array (u64) after the growslice call
        if kind == "b":
            c = next(i for i in range(g + 1, len(L)) if L[i] == "callq runtime.memmove")
        else:
            c = next(i for i in range(g + 1, len(L)) if STORE.fullmatch(L[i]))
        blk = range(start, c + 1)
        lt = [i for i in blk if re.fullmatch(r"cmpq \$0x[0-9a-f]+,0x[0-9a-f]+\(%\w+\)", L[i])]
        ct = [i for i in blk if re.fullmatch(r"cmp %\w+,%\w+", L[i]) and i < g
              and re.match(r"j(ae|b) ", next(L[x] for x in range(i + 1, len(L)) if L[x] != "nop"))]
        assert len(ct) == 1, (t, name, ct)
        ci = ct[0]
        cb = next(x for x in range(ci + 1, len(L)) if L[x] != "nop")
        newlen, cap = re.fullmatch(r"cmp %(\w+),%(\w+)", L[ci]).groups()
        ltxt = "none"
        recv = set()
        if lt:
            assert len(lt) == 1, (t, name, lt)
            li = lt[0]
            lb = next(x for x in range(li + 1, len(L)) if L[x] != "nop")
            ltxt = f"`{L[li]}` ({n(li)}); `{L[lb]}` ({n(lb)}) -> line {lab[target(L[lb])]}"
            assert int(L[li].split("$")[1].split(",")[0], 16) == size, (t, name)
            recv.add(re.search(r"\(%(\w+)\)", L[li])[1])
        # field load: `mov <goff>(%R),%x` (data pointer or the uint64 value) before the capacity test
        fl = [i for i in blk if i < ci and "(%rsp)" not in L[i] and re.fullmatch(rf"mov {goff:#x}\(%\w+\),%\w+" if goff else
                                                       r"mov \(%\w+\),%\w+", L[i])]
        assert len(fl) == 1, (t, name, fl)
        fr = re.search(r"\(%(\w+)\)", L[fl[0]])[1]
        if lt:
            assert next(iter(recv)) == fr, (t, name, recv, fr)
        rl = [i for i in blk if i < fl[0] and re.fullmatch(rf"mov 0x[0-9a-f]+\(%rsp\),%{fr}", L[i])]
        recv = [f"{fr} (field load `{L[fl[0]]}` ({n(fl[0])}))"] + [f"reloaded by `{L[i]}` ({n(i)})" for i in rl[-1:]]
        br = L[cb].split()[0]
        ctxt = (f"`{L[ci]}` ({n(ci)}); `{L[cb]}` ({n(cb)}) -> line {lab[target(L[cb])]} "
                f"({'fast path jumps' if br == 'jae' else 'growslice path jumps'})")
        if kind == "b":
            dst = [i for i in range(g + 1, c) if re.fullmatch(r"(lea \(%\w+,%\w+,1\),%rax|add %\w+,%rax)", L[i])]
            pc = next(x for x in range(c - 1, g, -1) if L[x] != "nop")
            dtxt = "; ".join(f"`{L[i]}` ({n(i)})" for i in dst) + (f"; `{L[pc]}` ({n(pc)})" if pc not in dst else "")
            kd = f"byte append {size}, memmove call"
        else:
            dtxt = f"`{L[c]}` ({n(c)})"
            kd = "uint64 inline store" + (" via zeroed stack temp" if any(L[i].startswith("movups %xmm15") for i in blk)
                                          else "")
        mn = tuple(MNEM.match(L[i])[1] for i in blk if L[i] and not L[i].endswith(":") and L[i] != "nop")
        forms.append((kind, mn))
        out.append(f"| {k} | {name} (Go +{goff:#x}, {gty}) | {kd} | {n(start)}–{n(c)} | {ltxt} | {ctxt} | {n(g)} `{L[g - 2]}`; "
                   f"`{L[g - 1]}` | `{L[c]}` ({n(c)}) | {'; '.join(recv)} | {newlen} / {cap} | {dtxt} |")
        start = c + 1
    # epilogue: from the last commit to the first retq
    r = next(i for i in range(start, len(L)) if L[i] == "retq")
    ep = range(start, r + 1)
    out.append("")
    out.append(f"Epilogue (lines {n(start)}–{n(r)}): " + "; ".join(f"`{L[i]}`" for i in ep if L[i] != "nop") + ".")
    eb = [i for i in ep if re.match(r"j(b|ae|ne|e|be) ", L[i])]
    for i in eb:
        out.append(f"Epilogue branch: `{L[i]}` (line {n(i)}) -> line {lab[target(L[i])]}.")
    calls = {}
    for i, l in enumerate(L):
        if l.startswith("callq "):
            calls.setdefault(l.split()[1], []).append(n(i))
    fast = {}
    for i in range(sub, r + 1):
        if L[i].startswith("callq "):
            fast.setdefault(L[i].split()[1], []).append(n(i))
    gsl = {n(g) for g in gs}
    out.append("Runtime callees in the function (call lines): "
               + "; ".join(f"`{k}` {v}" for k, v in sorted(calls.items())) + ".")
    inl = {k: [x for x in v if x not in gsl] for k, v in fast.items() if k != "runtime.growslice"}
    out.append("Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes "
               "these lines unless a branch above jumps over them): "
               + ("; ".join(f"`{k}` {v}" for k, v in sorted(inl.items()) if v) or "none") + ".")
    rej = sorted({lab[target(L[i])] for i in range(len(L)) if L[i].startswith("jne ")})
    out.append("Length-reject targets (jne): " + (", ".join(f"line {x}" for x in rej)
                                                  + "; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`."
                                                  if rej else "none."))
    nops = [n(i) for i, l in enumerate(L) if l == "nop"]
    out.append(f"`nop` lines: {nops}.")
    out.append("")
    return out, forms


def main(dest):
    body, allforms = [], []
    for t, d in TYPES:
        o, fm = survey(t, d)
        body += o
        allforms += [(t, k, m) for k, m in fm]
    u = {}
    b = {}
    for t, k, m in allforms:
        (u if k == "u64" else b).setdefault(m, []).append(t)
    head = [
        "# ENC2 survey: MarshalSSZTo of the 16 flat development types (Go 1.26.10 ELF `c6403c02…911e`)",
        "",
        "Unit E2-P (preparation; no proof). Facts read from the committed `.S` files by "
        "`gen/e2e/enc2survey.py` (run from `fv/kraken`).",
        "Checkpoint: `e2e/link`; BeaconBlockHeader: `e2e/bh/link`; Eth1Data: `e2e/e1/link`; the other 13: "
        "`e2e/enc2/link` (bundle in its `RESULT`).",
        "Field name, Go offset, kind and size come from `prysm/ir/ir-mainnet.json` (v1alpha1); sizes are checked "
        "against the length-test immediates, the field count against the growslice count.",
        "Register conventions at entry (Go ABIInternal): receiver `%rax`; dst ptr `%rbx`, len `%rcx`, cap `%rdi`.",
        "\"capacity test\" = `cmp %newlen,%cap` before the field's growslice; `jae` jumps when cap >= newlen "
        "(unsigned); `jb` jumps to the growslice path.",
        "\"receiver reg\" = base register of the block's load at the Go field offset (and its last reload from the frame before it).",
        "No primitives `MarshalSSZTo` is called (overlay fields are in-line stores); see "
        "`e2e/enc2/callgraph.json`.",
        "",
        "## Summary of distinct forms (mnemonic sequence of the field block, `nop` removed)",
        "",
        f"- uint64 store blocks: {sum(len(v) for v in u.values())} fields, {len(u)} distinct forms.",
    ]
    for i, (m, ts) in enumerate(sorted(u.items(), key=lambda x: -len(x[1]))):
        head.append(f"  - U{i} ({len(ts)}: {', '.join(ts)}): `{' '.join(m)}`")
    head.append(f"- byte-append blocks: {sum(len(v) for v in b.values())} fields, {len(b)} distinct forms.")
    for i, (m, ts) in enumerate(sorted(b.items(), key=lambda x: -len(x[1]))):
        head.append(f"  - B{i} ({len(ts)}: {', '.join(ts)}): `{' '.join(m)}`")
    head += ["- overlay (Slot, Epoch, ValidatorIndex, ... typed uint64): in-line (no call).", "", "## Per type", ""]
    pathlib.Path(dest).write_text("\n".join(head + body))
    print(f"uint64 forms {len(u)} byte forms {len(b)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
