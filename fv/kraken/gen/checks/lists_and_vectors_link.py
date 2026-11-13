#!/usr/bin/env python3
"""Call graph and link tables of the real v1alpha1.SyncAggregate, v1alpha1.SyncCommittee and
v1alpha1.IndexedAttestation UnmarshalSSZ on the Go 1.26.10 ELF (the same ELF as prysm/go1.26.10/link-set, sha256 c6403c02...911e).
A new file with the text of `deposit_data_and_pending_partial_withdrawal_link.py`: the function set and the data items changed. Existing scripts
(`checkpoint_and_epoch_link.py`, `attestation_data_link.py`, `deposit_data_and_pending_partial_withdrawal_link.py`, `link/convert_objdump.py`, `link/data.py`, `link/check.py`) are not changed.

Usage (Python 3 standard library only; python3 -I -B; the steps after `filter` are gated):
  lists_and_vectors_link.py callgraph <objdump> <out.json>          call targets with contract class
  lists_and_vectors_link.py filter <outdir> <objdump> <elf> <nm> [--with-indexed-attestation]
                                                    <outdir>/target.objdump of SyncAggregate, SyncCommittee (with --with-indexed-attestation: and IndexedAttestation)
                                                    (+ ELF/nm links)
  lists_and_vectors_link.py data <outdir> <checkpoint-link-dir> <attestation-data-link-dir> [--with-indexed-attestation]
                                                    after `convert_objdump.py <outdir>/target.objdump
                                                    <outdir>/p1bin-amd64.nm <outdir>/norm --norm`:
                                                    write <outdir>/data/*.data (link/data.py's code)
Then `link/check.py <outdir>` (a)-(f). Committed copy: prysm/go1.26.10/link-set (SyncAggregate, SyncCommittee only).
IndexedAttestation is linked only with --with-indexed-attestation: its .S has `lea 0xffffff1c(%rdi),%rdx` (GNU objdump spelling of the
displacement -228), which Apple clang 21 rejects in check (d).
Encoders, SizeSSZ and HashTreeRoot are not in the set (out of the list/vector scope).

Every data item is located from the converted code (the operand that the proofs read), not written by hand.
Operands that equal an item of the Checkpoint / Epoch link set (`checkpoint_and_epoch_link.py`) are asserted equal and get no
new file: the theorems use the existing `Prysm.ElfData.PrysmTarget` names for them (uint8 type word, ssz.ErrSize, type:int,
errors.errorString type and itab).
"""
import importlib.util
import json
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
LINK = HERE.parent.parent / "link"
sys.path.insert(0, str(HERE))
import checkpoint_and_epoch_link  # noqa: E402
import attestation_data_link  # noqa: E402

V1A1 = "github.com/OffchainLabs/prysm/v7/proto/prysm/v1alpha1"
FUNCS = [f"{V1A1}.(*SyncAggregate).UnmarshalSSZ", f"{V1A1}.(*SyncCommittee).UnmarshalSSZ",
         f"{V1A1}.(*IndexedAttestation).UnmarshalSSZ"]
SCOPE = {FUNCS[0]: "in (SyncAggregate decoder)", FUNCS[1]: "in (SyncCommittee decoder)", FUNCS[2]: "in (IndexedAttestation decoder)"}
CLASS = dict(attestation_data_link.CLASS)
CLASS.update({
    "runtime.makeslice": ("b", "MakesliceContract: esz 1 (uint8 type word, cnt 48/64/96), esz 24 (SyncCommittee "
                               "[][]byte, cnt 512), esz 8 (IndexedAttestation []uint64, cnt = numElem)"),
    "runtime.memmove": ("b", "MemmoveContract (n = 48, 64, 96)"),
    "runtime.panicBounds": ("a", "bounds check proved not taken in every loop iteration (fv_iter / lu_iter idiom)"),
    "runtime.convT64": ("b", "ConvT64Contract (IndexedAttestation misaligned / ssz-max rejects only)"),
    "runtime.newobject": ("b", "NewobjectContract: IndexedAttestation Data (AttestationData type word); after "
                               "fmt.errorf: the nil-result branch, excluded by rax != 0"),
    "fmt.errorf": ("b", "IndexedAttestation only: FmtErrorfDecimalWrapContract (two '%d ... %w' formats), FmtErrorfWrapContract "
                        "('Data: %w')"),
    f"{V1A1}.(*AttestationData).UnmarshalSSZ": ("a", "machine code in the host (Prysm.AttestationData.Decode.accept); "
                                                    "no AttestationData function-spec form exists"),
})


def callgraph(objdump, out):
    want, cur = set(FUNCS), None
    res = {f: {"addr": None, "instructions": 0, "calls": [], "scope": SCOPE[f]} for f in FUNCS}
    for line in open(objdump):
        if line.startswith("TEXT "):
            name = line.split()[1].removesuffix("(SB)")
            cur = name if name in want else None
            continue
        if cur is None or not line.strip():
            continue
        mm = re.match(r"\s*\S+:\d+\s+0x([0-9a-f]+)\s", line)
        if not mm:
            continue
        addr = int(mm[1], 16)
        r = res[cur]
        if r["addr"] is None:
            r["addr"] = addr
        r["instructions"] += 1
        m = re.search(r"CALL (\S+)\(SB\)", line)
        if m:
            c = CLASS.get(m[1])
            r["calls"].append({"site": hex(addr), "target": m[1], "class": c[0] if c else "UNCLASSIFIED",
                               "how": c[1] if c else ""})
    counts = {f: {} for f in FUNCS}
    for f in FUNCS:
        for c in res[f]["calls"]:
            counts[f][c["target"]] = counts[f].get(c["target"], 0) + 1
    unc = [(f, c["target"]) for f in FUNCS for c in res[f]["calls"] if c["class"] == "UNCLASSIFIED"
           and SCOPE[f].startswith("in")]
    missing = [f for f in FUNCS if res[f]["addr"] is None]
    for f in FUNCS:
        res[f]["addr"] = hex(res[f]["addr"]) if res[f]["addr"] is not None else None
    doc = {"functions": res, "call_counts": counts, "unclassified_in_scope": unc, "missing": missing}
    json.dump(doc, open(out, "w"), indent=1)
    for f in FUNCS:
        print(f"{f.split('/')[-1]:58} {res[f]['instructions']:4} instr  {counts[f]}")
    print("unclassified", unc, "missing", missing)
    return 1 if (missing or unc) else 0


def filt(outdir, objdump, elf, nm, with_indexed_attestation=False):
    checkpoint_and_epoch_link.callgraph.FUNCS = FUNCS if with_indexed_attestation else FUNCS[:2]
    return checkpoint_and_epoch_link.filt(outdir, objdump, elf, nm)


def items(outdir, checkpoint_dir, attestation_data_dir, with_indexed_attestation=False):
    """SyncAggregate: two makeslice (uint8, cap 64 and 96) and two memmove; no fmt.errorf / newobject /
    growslice. SyncCommittee: one makeslice of the [][]byte backing array (its own type word, esz 24,
    cnt 512), then one uint8 makeslice per element and one for AggregatePubkey; no fmt.errorf / newobject /
    growslice. IndexedAttestation: makeslice of []uint64 (its own type word), the two convT64 + fmt.errorf
    list rejects ('%d ... %w', type:int box), newobject of the AttestationData object (its own type word),
    the AttestationData call, the 'Data: %w' wrap, makeslice + memmove of Signature.
    New data files: the three type words (48-byte abi.Type, data.ABI_TYPE_WORDS), the three format strings,
    the three error globals other than ssz.ErrSize (address only, length 0)."""
    spec = importlib.util.spec_from_file_location("data", LINK / "data.py")
    data = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(data)
    V = "github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1"
    sync_aggregate_lines = checkpoint_and_epoch_link.ins(outdir, f"{V}.SyncAggregate.UnmarshalSSZ")
    sync_committee_lines = checkpoint_and_epoch_link.ins(outdir, f"{V}.SyncCommittee.UnmarshalSSZ")
    cu = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.CHECKPOINT_SYMBOL}.UnmarshalSSZ")
    eu = checkpoint_and_epoch_link.ins(checkpoint_dir, f"{checkpoint_and_epoch_link.EPOCH_SYMBOL}.UnmarshalSSZ")
    au = checkpoint_and_epoch_link.ins(attestation_data_dir, f"{V}.AttestationData.UnmarshalSSZ")
    lea = r"lea ([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%{}"
    back = attestation_data_link.back_lea
    u8 = checkpoint_and_epoch_link.operand([cu[cu.index("callq runtime.makeslice") - 3]], lea.format("rax"))
    wb = r"cmpl \$0x0,([A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\)"
    esz = checkpoint_and_epoch_link.operand(cu, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()")
    estype = back(cu, cu.index("callq runtime.newobject"))
    itab = checkpoint_and_epoch_link.operand(cu, r"lea (go_itab[A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax")
    # type:int of the Epoch reject (`checkpoint_and_epoch_link.items`: the first `lea X(%rip),%rdx` of the Epoch decoder)
    inttype = [checkpoint_and_epoch_link.operand([l], lea.format("rdx")) for l in eu if re.fullmatch(lea.format("rdx"), l)][0]

    def mk_types(lines):
        """Type word of every makeslice: the nearest `lea X(%rip),%rax` in the 5 lines before the call."""
        out = []
        for i, l in enumerate(lines):
            if l == "callq runtime.makeslice":
                ts = [checkpoint_and_epoch_link.operand([lines[j]], lea.format("rax")) for j in range(i - 5, i)
                      if re.fullmatch(lea.format("rax"), lines[j])]
                assert len(ts) == 1, ("makeslice type word", i, ts)
                out.append(ts[0])
        return out

    def no_calls(lines, names):
        assert not any(l in [f"callq {n}" for n in names] for l in lines), names

    its = []
    # SyncAggregate
    assert mk_types(sync_aggregate_lines) == [u8, u8], mk_types(sync_aggregate_lines)
    assert sum(l == "callq runtime.memmove" for l in sync_aggregate_lines) == 2
    no_calls(sync_aggregate_lines, ["fmt.errorf", "runtime.newobject", "runtime.growslice", "runtime.panicBounds"])
    assert checkpoint_and_epoch_link.operand(sync_aggregate_lines, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz
    assert checkpoint_and_epoch_link.operand(sync_aggregate_lines, wb) == checkpoint_and_epoch_link.operand(au, wb)
    # SyncCommittee: the first makeslice has its own type word ([]byte element of [][]byte)
    st = mk_types(sync_committee_lines)
    assert len(st) == 3 and st[0] != u8 and st[1:] == [u8, u8], st
    assert sum(l == "callq runtime.memmove" for l in sync_committee_lines) == 2
    assert sum(l == "callq runtime.panicBounds" for l in sync_committee_lines) == 1
    no_calls(sync_committee_lines, ["fmt.errorf", "runtime.newobject", "runtime.growslice"])
    assert checkpoint_and_epoch_link.operand(sync_committee_lines, r"mov ([A-Za-z0-9_.]+)\(%rip\),%rax()") == esz
    assert checkpoint_and_epoch_link.operand(sync_committee_lines, wb) == checkpoint_and_epoch_link.operand(au, wb)
    its.append(("typeUint8Slice", st[0][0], st[0][1], 48, data.ABI_TYPE_WORDS))
    if not with_indexed_attestation:
        return data, its
    # IndexedAttestation
    ia = checkpoint_and_epoch_link.ins(outdir, f"{V}.IndexedAttestation.UnmarshalSSZ")
    it = mk_types(ia)
    assert len(it) == 2 and it[0] != u8 and it[1] == u8, it
    its.append(("typeUint64", it[0][0], it[0][1], 48, data.ABI_TYPE_WORDS))
    no_calls(ia, ["runtime.growslice"])
    nobj = [i for i, l in enumerate(ia) if l == "callq runtime.newobject"]
    nty = [back(ia, i) for i in nobj]
    adt = [t for t in nty if t != estype]
    assert len(adt) == 1 and nty.count(estype) == 3, nty
    its.append(("typeAttestationData", adt[0][0], adt[0][1], 48, data.ABI_TYPE_WORDS))
    cvt = [i for i, l in enumerate(ia) if l == "callq runtime.convT64"]
    assert len(cvt) == 2
    for i in cvt:
        assert checkpoint_and_epoch_link.operand([ia[i + 1]], lea.format("rcx")) == inttype, ("type:int", i)
    assert checkpoint_and_epoch_link.operand(ia, r"lea (go_itab[A-Za-z0-9_.]+)(?:\+(\d+))?\(%rip\),%rax") == itab
    assert checkpoint_and_epoch_link.operand(ia, r"mov (ssz\.ErrSize)\(%rip\),%rax()") == esz
    assert checkpoint_and_epoch_link.operand(ia, wb) == checkpoint_and_epoch_link.operand(au, wb)
    assert sum(l == f"callq {V}.AttestationData.UnmarshalSSZ" for l in ia) == 1

    def fmts(lines):
        out = []
        for i, l in enumerate(lines):
            if l == "callq fmt.errorf":
                k = next(j for j in range(i - 1, i - 8, -1) if re.fullmatch(r"mov \$0x[0-9a-f]+,%ebx", lines[j]))
                out.append((checkpoint_and_epoch_link.operand([lines[k - 1]], lea.format("rax")),
                            int(re.fullmatch(r"mov \$0x([0-9a-f]+),%ebx", lines[k])[1], 16)))
        return out
    f3 = fmts(ia)
    # "ssz-max exceeded: ... %d ... %w", "misaligned bytes: ... %d ... %w", "Data: %w" (code order)
    assert [n for _, n in f3] == [0x49, 0x53, 8], f3
    its.append((None, f3[0][0][0], f3[0][0][1], f3[0][1], []))
    its.append((None, f3[1][0][0], f3[1][0][1], f3[1][1], []))
    its.append((None, f3[2][0][0], f3[2][0][1], f3[2][1], []))
    for g in ("ErrListTooBig", "ErrIncorrectListSize", "ErrInvalidVariableOffset"):
        assert any(re.fullmatch(rf"mov ssz\.{g}\(%rip\),%r[a-z]+", l) for l in ia), g
        its.append((None, f"ssz.{g}", 0, 0, []))
    return data, its


def write_data(outdir, checkpoint_dir, attestation_data_dir, with_indexed_attestation=False):
    data, its = items(outdir, checkpoint_dir, attestation_data_dir, with_indexed_attestation)
    for it in its:
        print("item", it[:4])
    data.ITEMS = its
    data.main(pathlib.Path(outdir))
    return 0


if __name__ == "__main__":
    c = sys.argv[1]
    if c == "callgraph":
        sys.exit(callgraph(*sys.argv[2:4]))
    with_indexed_attestation = "--with-indexed-attestation" in sys.argv
    if c == "filter":
        sys.exit(filt(*sys.argv[2:6], with_indexed_attestation=with_indexed_attestation))
    if c == "data":
        sys.exit(write_data(*sys.argv[2:5], with_indexed_attestation=with_indexed_attestation))
    sys.exit(f"unknown command {c}")
