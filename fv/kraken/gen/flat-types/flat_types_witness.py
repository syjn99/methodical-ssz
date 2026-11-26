"""Write the decoder witness modules WitnessGeneratedDecodeRejectSize (rows of gen/generator/types.tsv with the
companion `reject-witness`) and WitnessGeneratedDecodeAccept (rows with the companion `accept-witness`) in
lean/Prysm/<GoTypeName>/ (non-vacuity of the generated size-reject / accept theorems).
The accept witnesses have three forms: frame 0x38 (SyncAggregatorSelectionData), frame 0x20 without callee
(Deposit_Data), and the frame with slices and callees (PendingDeposit).
The memory block of each type is laid out here from the frame facts of its `.S`, with the addresses computed below.
usage: python3 -I -B flat_types_witness.py <fv/kraken>"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'generator'))
from flat_types_spec import spec_entry, with_code_imports  # noqa: E402
import types_table  # noqa: E402

CALLEE = {'Slot': ('Prysm.Slot.Code.unmarshalSSZ', 'primitives.Slot'), 'ValidatorIndex': ('Prysm.ValidatorIndex.Code.unmarshalSSZ', 'primitives.ValidatorIndex'),
          'Epoch': ('Prysm.Epoch.Code.unmarshalSSZ', 'primitives.Epoch')}


def entry(table, X, name):
    """`table[X]`, or a stop with a message for a table type without an entry in the table `name` of the form."""
    if X not in table:
        sys.exit(f'flat_types_witness: {X} is a type of gen/generator/types.tsv without an entry in the table {name} of accbytes')
    return table[X]


# The form of the accept witness of each type of the table: the frame of its decoder code (NEW-TYPE.md section 6).
FRAME_FORM = {'BeaconBlocksByRangeRequest': 'frame_0x38', 'BlobSidecarsByRangeRequest': 'frame_0x38',
              'ExecutionPayloadEnvelopesByRangeRequest': 'frame_0x38',
              'DepositRequest': 'no_callee_frame_0x20', 'BuilderDepositRequest': 'no_callee_frame_0x20',
              'PartialDataColumnGroupID': 'slices_and_callees', 'ValidatorIdentity': 'slices_and_callees',
              'SyncAggregatorSelectionData': 'frame_0x38', 'Deposit_Data': 'no_callee_frame_0x20',
              'PendingDeposit': 'slices_and_callees', 'Status': 'slices_and_callees'}
CLEN, BUMPLEN, RTLEN = 63, 6, 26


def slen(kr, row):
    f = os.path.join(kr, types_table.assembly(row))
    return sum(1 for l in open(f) if l.strip())


def nest(items):
    s = items[-1]
    for it in reversed(items[:-1]):
        s = f'{it} ++ ({s})'
    return s


def hexs(a):
    return '0x%x' % a


# ---------------------------------------------------------------- reject witnesses (every type; frame-independent)
def reject(X, n):
    ty, fs, _ = spec_entry(X, 'flat_types_witness')
    N = sum(f[2] for f in fs)
    L = 1 + n
    return f'''module

public import Prysm.{X}.GeneratedDecodeAccept
public import Runtime.CopyModel
public import Machine.WitnessHost

@[expose] public section

/-!
# Witness of the generated `Decode.generated_reject`

Host: the label `ssz.ErrSize` (index 0), then the Go 1.26.10 `(*{ty}).UnmarshalSSZ` (index 1).
Written by `gen/flat-types/flat_types_witness.py`.
It applies the generated size-reject theorem of `Prysm/{X}/GeneratedDecodeAccept.lean`. Memory at
`0x10000`: the two words of `ssz.ErrSize` after package init (a non-zero itab word `0x10e8` and a data word `0x2a`,
stand-ins: the Go runtime sets the values at start, and the ELF does not hold them), the guard word, saved-rbp
slot, return slot, the unused rax spill slot (the frame `R`) and the rbx spill slot. For every length `≠ {N}`
(instances {N - 1}, {N + 1}, 0) the decoder returns the two words.
-/

open Machine Runtime Machine.Witness Prysm.{X}.Code

open Codec
namespace Prysm.{X}.Witness.GeneratedDecodeRejectSize

set_option maxRecDepth 100000

def program : Program := [.label "ssz.ErrSize"] ++ unmarshalSSZ

theorem program_length : program.length = {L} := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrSize"] [] (by simp [Host.prog, mkHost, program]) rfl

theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by decide)

theorem label_err_size : label "ssz.ErrSize" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrSize word 0 · word 1 · guard (r14 = 0x10000) · saved rbp · return slot (rsp = 0x10020) · spill rax · spill rbx. -/
def block : List UInt8 := word_bytes 0x10e8 ++ (word_bytes 0x2a ++ (word_bytes 0 ++ (zeros 8 ++ (word_bytes 0 ++ (zeros 8 ++ zeros 8)))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def initial_state (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10100, 0x10200, len, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem⟩

def frame_rest : DataMem → Prop := Eq ((zeros 8).At (0x10028 : BitVec 64))

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of the generated `Decode.generated_reject`.** -/
theorem runs (len : UInt64) (hlen : len ≠ {N}) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨initial_state len zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Prysm.{X}.Decode.generated_reject 1 placed_at_1 labels_fresh_at_1 (initial_state len zmms flags) 0 0 0x10e8 0x2a (zeros 8) (zeros 8) rfl rfl frame_rest
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      witness_split []
      simp only [initial_state, frame_rest, word_bytes, ElfData.PrysmTarget.sszErrSize_addr, label_err_size, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      sep_perm H)
    (by simp [initial_state]) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs {N - 1} (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs {N + 1} (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := runs 0 (by decide) z' f

end Prysm.{X}.Witness.GeneratedDecodeRejectSize
'''


# ---------------------------------------------------------------- accept witness, callee frame 0x38 (u64 fields only)
def accept_witness_frame_0x38(X, n):
    """SyncAggregatorSelectionData frame (sub $0x38; Slot call first, then in-line u64). nf input words."""
    ty, fs, _ = spec_entry(X, 'flat_types_witness')
    nf = len(fs)
    N = 8 * nf
    plen = 1 + n + CLEN
    ins = [f'in{i}' for i in range(nf)]
    # guard 0x10000 · inputs at 0x10008 · [8 unused if nf = 2] · receiver at 0x10020 (state, nf words, tail 32) …
    gap = 8 if nf == 2 else 0
    assert 8 + N + gap == 0x20
    rcv = 0x10020
    tail = rcv + 8 + N
    tail_len = 32 + (8 if nf == 2 else 0)   # Sa: tail 32 + 8 unused = 40
    assert tail + tail_len == 0x10060
    blk = ['zero_word_bytes'] + ins + (['zeros 8'] if gap else []) + ['zeros 8'] * (1 + nf) + [f'zeros {tail_len}'] + \
        ['zeros 8', 'zeros 8', 'zeros 8', 'zeros 8', 'zeros 40', 'zeros 8', 'zero_word_bytes', 'zeros 8', 'zeros 8']
    R0 = (f'Eq ((zeros {tail_len}).At ({hexs(tail)} : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10070 : BitVec 64))\n'
          '    ⋆ Eq ((zeros 40).At (0x10080 : BitVec 64))')
    if gap:
        R0 = 'Eq ((zeros 8).At (0x10018 : BitVec 64)) ⋆ ' + R0
    nlist = 7 + nf
    zs = ' '.join(['(zeros 8)'] * nlist)
    rfls = ' '.join(['rfl'] * nlist)
    hins = ' '.join(f'(hin{i} : in{i}.length = 8)' for i in range(nf))
    insp = ' '.join(ins)
    hinsn = ' '.join(f'hin{i}' for i in range(nf))
    z8s = ' '.join(['(zeros 8)'] * nf)
    rr = ' '.join(['rfl'] * nf)
    reps = ' '.join(f'(Int.toBytes 8 {v})' for v in ['0x0123456789abcdef', '7', '0x40'][:nf])
    decs = ' '.join(['(by decide)'] * nf)
    ffs = ' '.join(['(List.replicate 8 0xff)'] * nf)
    return f'''module

public import Prysm.{X}.GeneratedDecodeAccept
public import Runtime.CopyModel
public import Machine.WitnessHost

@[expose] public section

/-!
# Witness of the generated `Decode.generated_accept` (`{ty}` decoder accept path)

Written by `gen/flat-types/flat_types_witness.py`, for the frame `0x38` with one Slot callee and {nf} input words.
It shows that the premises of
the generated accept theorem (statement = kind instance) are satisfiable. Host: one label, the Go 1.26.10
`(*{ty}).UnmarshalSSZ` (index 1) and `primitives.Slot` UnmarshalSSZ ({1 + n}).
One memory block at `0x10000`: guard · input ({nf} × 8){' · 8 unused' if gap else ''} · receiver (state, {nf} fields,
then the untouched tail) · callee frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee
rbx spill (rsp − 56) · 40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx. The receiver is
at rax = 0x10020 (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, fields at 8 …). The frame
`R` is the untouched receiver tail and frame ranges. For every {N}-byte input every premise holds and the decoder
returns nil. The receiver is a Go value of `{ty}` (all zero).
-/

open Machine Runtime Machine.Witness Codec Prysm.{X}.Code

namespace Prysm.{X}.Witness.GeneratedDecodeAccept

set_option maxRecDepth 100000

def program : Program := [.label "pad0"] ++ unmarshalSSZ ++ Prysm.Slot.Code.unmarshalSSZ

theorem program_length : program.length = {plen} := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_1 : unmarshalSSZ.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.Slot.Code.unmarshalSSZ) (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem labels_fresh_at_1 : LabelsFresh unmarshalSSZ 1 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem placed_at_{1 + n} : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog {1 + n} :=
  infixAt_of ([.label "pad0"] ++ unmarshalSSZ) ([])
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_{1 + n} : LabelsFresh Prysm.Slot.Code.unmarshalSSZ {1 + n} := labelsFresh_of (by rw [host_program_eq]; decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block ({insp} : List UInt8) : List UInt8 :=
  {nest(blk)}

def mem ({insp} : List UInt8) : DataMem := (block {insp}).At (0x10000 : BitVec 64)

def initial_state ({insp} : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, {N}, 0, 0, {N}, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem {insp}⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def frame_rest : DataMem → Prop :=
  {R0}

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `Decode.generated_accept`** (premises of the kind instance). -/
theorem runs ({insp} : List UInt8) {hins}
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state {insp} zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (Prysm.{X}.Decode.generated_accept 1 placed_at_1 labels_fresh_at_1 {1 + n} placed_at_{1 + n} labels_fresh_at_{1 + n}
    {insp} {hinsn} (initial_state {insp} zmms flags)
    0 0 {zs}
    {rfls}
    frame_rest
    (by
      have H : Eq ((block {insp}).At (0x10000 : BitVec 64)) (mem {insp}) := rfl
      witness_split [{', '.join(f'hin{i}' for i in range(nf))}]
      simp only [initial_state, frame_rest, zero_word_bytes, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      sep_perm H)
    (by simp [initial_state]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := runs {z8s} {rr} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs {reps} {decs} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs {ffs} {rr} z' f

end Prysm.{X}.Witness.GeneratedDecodeAccept
'''


# ---------------------------------------------------------------- accept witness, byte fields (+ callees)
def accbytes(X, n, frame):
    """frame 'no_callee_frame_0x20': the Deposit_Data frame (sub $0x20, no call; S = 16);
    frame 'slices_and_callees': slices and callees (S = 8), the frame F of the type."""
    ty, fs, _ = spec_entry(X, 'flat_types_witness')
    N = sum(f[2] for f in fs)
    heap = sum(f[2] for f in fs if f[1] == 'b')
    nb = sum(1 for f in fs if f[1] == 'b')
    gsize = entry({'DepositRequest': 128, 'BuilderDepositRequest': 120, 'PartialDataColumnGroupID': 72, 'ValidatorIdentity': 80,
                   'Deposit_Data': 120, 'PendingDeposit': 128, 'Status': 128}, X, 'gsize')
    callees = entry({'DepositRequest': [], 'BuilderDepositRequest': [], 'PartialDataColumnGroupID': ['Slot'], 'ValidatorIdentity': ['ValidatorIndex', 'Epoch'],
                     'Deposit_Data': [], 'PendingDeposit': ['Slot'], 'Status': ['Epoch', 'Slot']}, X, 'callees')
    ins = [f'f{i}' for i in range(len(fs))]
    ops = [f'oP{j + 1}' for j in range(nb)]
    params = ins + ops
    # addresses
    guard = 0x1000c + heap
    rbx = guard + 8
    rax = rbx + N
    # receiver words (state at 0; per field: u64 word or (ptr, len, cap))
    rwords, rnames = ['zeros 8'], []
    j = 0
    for f in fs:
        if f[1] == 'u':
            rwords.append('zeros 8')
            rnames.append('(zeros 8)')
        else:
            rwords += [ops[j], 'zeros 8', 'zeros 8']
            rnames += [ops[j], '(zeros 8)', '(zeros 8)']
            j += 1
    rlen = 8 * len(rwords)
    tail = gsize - rlen
    assert tail == 32, (X, tail)
    endr = rax + gsize
    if frame == 'no_callee_frame_0x20':
        S = 16
        F_lo = endr                      # lo (S bytes) = rsp - 48 - S
        rsp = F_lo + 48 + S
        # lo 16 · rslot · spl 24 · l18 · fp · ret · s1 · s2 · caller word
        stack = ['zeros 16', 'zeros 8', 'zeros 24', 'zeros 8', 'zeros 8', 'zero_word_bytes', 'zeros 8', 'zeros 8', 'zeros 8']
        R0 = f'Eq ((zeros 32).At ({hexs(rax + rlen)} : BitVec 64)) ⋆ Eq ((zeros 8).At ({hexs(rsp + 24)} : BitVec 64))'
        lists = ['(zeros 8)', '(zeros 8)', '(zeros 8)', '(zeros 24)', '(zeros 8)', '(zeros 8)', '(zeros 16)', '(zeros 8)'] + rnames
        lens = ['rfl'] * 7
        Sarg = '16 rfl'
        callargs = ''
    else:
        S = 8
        Fr = entry({'PartialDataColumnGroupID': 0x40, 'ValidatorIdentity': 0x50, 'PendingDeposit': 0x40, 'Status': 0x50}, X, 'Fr')
        rslot_off = Fr + 16              # return slot at rsp - (F + 16)
        F_lo = endr
        rsp = F_lo + rslot_off + 8 + S   # lo (S + 8) at rsp - rslot_off - 8 - S
        lsave = entry({'PartialDataColumnGroupID': 32, 'ValidatorIdentity': 48, 'PendingDeposit': 32, 'Status': 48}, X, 'lsave')
        # rsp - rslot_off - 8 - S: lo (16) · rslot · sp0 sp1 sp2 · gap1 · l28 · gap2 · fp · ret · s1 · s2 · unused · s4
        sp0 = rsp - rslot_off + 8        # = rsp - (F + 8)
        gap1 = sp0 + 24
        gap1_len = (rsp - lsave) - gap1
        gap2 = rsp - lsave + 8
        gap2_len = (rsp - 8) - gap2
        stack = ['zeros 16', 'zeros 8', 'zeros 8', 'zeros 8', 'zeros 8', f'zeros {gap1_len}', 'zeros 8', f'zeros {gap2_len}', 'zeros 8', 'zero_word_bytes', 'zeros 8', 'zeros 8',
                 'zeros 8', 'zeros 8']
        R0 = (f'Eq ((zeros 32).At ({hexs(rax + rlen)} : BitVec 64)) ⋆ Eq ((zeros {gap1_len}).At ({hexs(gap1)} : BitVec 64))'
              f' ⋆ Eq ((zeros {gap2_len}).At ({hexs(gap2)} : BitVec 64))\n    ⋆ Eq ((zeros 8).At ({hexs(rsp + 24)} : BitVec 64))')
        lists = ['(zeros 8)'] * 9 + ['(zeros 16)', '(zeros 8)'] + rnames
        lens = ['rfl'] * 10
        Sarg = '8 (by decide) rfl'
    lens2 = []
    j = 0
    for f in fs:
        if f[1] == 'u':
            lens2.append('rfl')
        else:
            lens2 += [f'h{j + 1}', 'rfl', 'rfl']
            j += 1
    blk = ['Int.toBytes 8 (0x1000c : BitVec 64).toInt', '[0, 0, 0, 0]', f'zeros {heap}', 'zero_word_bytes'] + ins + rwords + ['zeros 32'] + stack
    blk = [b if b in params or b in ('zero_word_bytes',) else f'({b})' for b in blk]
    # program
    b0 = 9 + n
    idx, prog, hks = b0, f'dataLabels ++ unmarshalSSZ', []
    cl = [CALLEE[c][0] for c in callees]
    tailp = cl + ['BumpMakeslice1', 'MemmoveGrowsliceModel']
    calls = []
    for c in cl:
        rest = ' ++ '.join(tailp[tailp.index(c) + 1:]) or '[]'
        hks.append(f'theorem placed_at_{idx} : {c}.IsInfixAt Host.prog {idx} :=\n  infixAt_of ({prog}) ({rest})\n'
                   f'    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)\n'
                   f'theorem labels_fresh_at_{idx} : LabelsFresh {c} {idx} := labelsFresh_of (by rw [host_program_eq]; decide)')
        calls.append(f'{idx} placed_at_{idx} labels_fresh_at_{idx}')
        prog += f' ++ {c}'
        idx += CLEN
    bi, ri = idx, idx + BUMPLEN
    plen = ri + RTLEN
    pp = ' '.join(params)
    hparams = ' '.join(f'(h{f[0]} : {f[0]}.length = {g[2]})' for f, g in zip([(p,) for p in ins], fs)) + ' ' + \
        ' '.join(f'(h{j + 1} : {o}.length = 8)' for j, o in enumerate(ops))
    hin = ' '.join(f'h{p}' for p in ins)
    wl = ', '.join([f'h{p}' for p in ins] + [f'h{j + 1}' for j in range(nb)])
    # examples
    def zero(f):
        return f'(zeros {f[2]})'

    def rep(i, f):
        if f[1] == 'u':
            return f'(Int.toBytes 8 0x0123456789abcde{i})'
        return f'((List.range {f[2]}).map (fun i => UInt8.ofNat (i + {10 * i})))'
    ex0 = ' '.join([zero(f) for f in fs] + ['(zeros 8)'] * nb + ['rfl'] * (len(fs) + nb))
    ex1 = ' '.join([rep(i, f) for i, f in enumerate(fs)] + [f'(Int.toBytes 8 0x{2 + j}0000)' for j in range(nb)]
                   + [('(by decide)' if f[1] == 'u' else 'rfl') for f in fs] + ['(by decide)'] * nb)
    ex2 = ' '.join([f'(List.replicate {f[2]} 0xff)' for f in fs] + ['(List.replicate 8 0xff)'] * nb
                   + ['rfl'] * (len(fs) + nb))
    opens = f'Machine Runtime Machine.Witness Codec Prysm.{X}.Code'
    cdoc = ', '.join(f'`{CALLEE[c][1]}` UnmarshalSSZ' for c in callees)
    return f'''module

public import Prysm.{X}.GeneratedDecodeAccept
public import Runtime.CopyModel
public import Runtime.BumpAllocatorVariants
public import Machine.WitnessHost

@[expose] public section

/-!
# Witness of the generated `Decode.generated_accept` (`{ty}` decoder accept path)

Written by `gen/flat-types/flat_types_witness.py`.
It shows that the premises of the generated accept theorem (statement = kind instance)
are satisfiable. Host: data labels, the Go 1.26.10 `(*{ty}).UnmarshalSSZ` (index 9){', ' + cdoc if cdoc else ''},
the 1-byte bump `runtime.makeslice` ({bi}, `bump_makeslice1`) and `MemmoveGrowsliceModel` ({ri}, `model_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the {heap}-byte heap, guard word, the {N} input bytes,
the {gsize}-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state`, per byte field a slice header with an
old pointer word and len = cap = 0, per uint64 field a zero word, then 32 untouched tail bytes), the callee block
(`S = {S}`), the return slot, the argument area, the untouched frame ranges, the slice pointer save, the saved rbp
and the caller's slots (rsp = {hexs(rsp)}). The frame `R` is the receiver tail, the untouched frame ranges and the
caller's word at rsp + 24. For every input and every old pointer word every premise holds and the decoder returns
nil. The receiver is a Go value of `{ty}` (zero `state`, zero-length slices, zero integers).
-/

open {opens}

namespace Prysm.{X}.Witness.GeneratedDecodeAccept

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := {prog} ++ BumpMakeslice1 ++ MemmoveGrowsliceModel

theorem program_length : program.length = {plen} := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels ({' ++ '.join(tailp)}) (by simp [host_program_eq, program, List.append_assoc]) rfl
{chr(10).join(hks)}
theorem placed_at_{bi} : BumpMakeslice1.IsInfixAt Host.prog {bi} :=
  infixAt_of ({prog}) MemmoveGrowsliceModel
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem placed_at_{ri} : MemmoveGrowsliceModel.IsInfixAt Host.prog {ri} :=
  infixAt_of ({prog} ++ BumpMakeslice1) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_{ri} : LabelsFresh MemmoveGrowsliceModel {ri} := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_{bi} : ∀ i < {bi}, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block ({pp} : List UInt8) : List UInt8 :=
  {nest(blk)}

def mem ({pp} : List UInt8) : DataMem :=
  (block {pp}).At (0x10000 : BitVec 64)

def initial_state ({pp} : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨{hexs(rax)}, {hexs(rbx)}, {N}, 0, 0, {N}, {hexs(rsp)}, 0, 0, 0, 0, 0, 0, 0, {hexs(guard - 16)}, 0⟩, zmms, flags,
    mem {pp}⟩

/-- The frame of the witness. -/
def frame_rest : DataMem → Prop :=
  {R0}

theorem lift_heap {{X : DataMem → Prop}} {{m : DataMem}}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros {heap}).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap {heap} ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `Decode.generated_accept`** (premises of the kind instance are satisfiable). -/
theorem runs ({pp} : List UInt8) {hparams}
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨initial_state {pp} zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (Prysm.{X}.Decode.generated_accept 9 placed_at_9 labels_fresh_at_9 {' '.join(calls)}
    {' '.join(ins)} {hin} (initial_state {pp} zmms flags)
    0 0 {' '.join(lists)}
    {' '.join(lens + lens2)}
    frame_rest {Sarg} bumpHeap {heap}
    (by
      have H : Eq ((block {pp}).At (0x10000 : BitVec 64)) (mem {pp}) := rfl
      witness_split [{wl}]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros {heap}).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, frame_rest, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      sep_perm H2)
    (by simp [initial_state]) rfl (Nat.le_refl _) (bump_makeslice1 {bi} placed_at_{bi} labels_fresh_at_{bi} _) (model_memmove {ri} placed_at_{ri} labels_fresh_at_{ri} _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with nil slices; a representative input with non-nil old pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  runs {ex0} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs {ex1} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs {ex2} z' f

end Prysm.{X}.Witness.GeneratedDecodeAccept
'''


if __name__ == '__main__':
    kr = sys.argv[1]
    for row in types_table.rows():
        X = row['type']
        if 'reject-witness' in row['companions']:
            n = slen(kr, row)
            d = os.path.join(kr, 'lean', 'Prysm', X)
            open(os.path.join(d, 'WitnessGeneratedDecodeRejectSize.lean'), 'w').write(with_code_imports(reject(X, n), X))
            print(X, 'reject', n)
        if 'accept-witness' not in row['companions']:
            continue
        if X not in FRAME_FORM:
            sys.exit(f'flat_types_witness: {X} is a type of gen/generator/types.tsv without an entry in FRAME_FORM')
        n = slen(kr, row)
        d = os.path.join(kr, 'lean', 'Prysm', X)
        if FRAME_FORM[X] == 'frame_0x38':
            a = accept_witness_frame_0x38(X, n)
        else:
            a = accbytes(X, n, FRAME_FORM[X])
        open(os.path.join(d, 'WitnessGeneratedDecodeAccept.lean'), 'w').write(with_code_imports(a, X))
        print(X, 'accept', n)
