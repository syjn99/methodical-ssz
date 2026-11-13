"""Evidence tool (not part of gen/scal): write the decoder witness modules WitnessGeneratedDecodeAccept and
WitnessGeneratedDecodeRejectSize (lean/Prysm/<GoTypeName>/) of the seven
generated decoders (non-vacuity of the generated accept / size-reject theorems). Texts follow the script
`mkwit.py` (reject; callee frame 0x38) and the hand witnesses `Prysm/Deposit_Data/WitnessDecodeAccept.lean` (frame 0x20 bytes) and `Prysm/PendingDeposit/WitnessDecodeAccept.lean`
(frame with slices and callees); the memory block of each type is laid out here from the frame facts of its `.S`
(the same facts as `Prysm/DepositRequest/Statements.lean`), with the addresses computed below.
usage: python3 -I -B f24wit.py <fv/kraken> [X ...]"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from f24spec import T, GO_TYPE, new_names  # noqa: E402

NORM = 'prysm/go1.26.10/link-set/norm'
SFILE = {'Dpr': 'engine_v1.DepositRequest', 'Bdr': 'engine_v1.BuilderDepositRequest',
         'Bbr': 'prysm_v1alpha1.BeaconBlocksByRangeRequest', 'Bsr': 'prysm_v1alpha1.BlobSidecarsByRangeRequest',
         'Epr': 'prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest',
         'Pdc': 'prysm_v1alpha1.PartialDataColumnGroupID', 'Vid': 'prysm_v1alpha1.ValidatorIdentity'}
CALLEE = {'Sl': ('Prysm.Slot.Code.unmarshalSSZ', 'primitives.Slot'), 'Vi': ('Prysm.ValidatorIndex.Code.unmarshalSSZ', 'primitives.ValidatorIndex'),
          'Ep': ('Prysm.Epoch.Code.unmarshalSSZ', 'primitives.Epoch')}
CLEN, BUMPLEN, RTLEN = 63, 6, 26


def slen(kr, X):
    f = os.path.join(kr, NORM, 'github.com_OffchainLabs_prysm_v7_proto_' + SFILE[X].replace('engine_v1', 'engine_v1')
                     .replace('prysm_v1alpha1', 'prysm_v1alpha1') + '.UnmarshalSSZ.S')
    return sum(1 for l in open(f) if l.strip())


def nest(items):
    s = items[-1]
    for it in reversed(items[:-1]):
        s = f'{it} ++ ({s})'
    return s


def hexs(a):
    return '0x%x' % a


# ---------------------------------------------------------------- reject witnesses (all seven; frame-independent)
def reject(X, n):
    ty, fs, _ = T[X]
    x = X.lower()
    N = sum(f[2] for f in fs)
    L = 1 + n
    return f'''import E2eScal.Gen5F24{X}Dec
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `{x}_g5dec_reject` (FLAT24 / H7)

Host: the label `ssz.ErrSize` (index 0), then the real Go 1.26.10 `(*{ty}).UnmarshalSSZ` (index 1).
Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of the G5-C reject witnesses
(`WitSaGR.lean`) with the {ty} decoder and the generated size-reject theorem of `Gen5F24{X}Dec.lean`. Memory at
`0x10000`: the two words of `ssz.ErrSize` after package init (a non-zero itab word `0x10e8` and a data word `0x2a`,
stand-ins: the real values are set by the runtime's init and are not read from the ELF), the guard word, saved-rbp
slot, return slot, the unused rax spill slot (the frame `R`) and the rbx spill slot. For every length `≠ {N}`
(instances {N - 1}, {N + 1}, 0) the decoder returns the two words.
-/

open Machine Runtime Machine.Witness Prysm.BuilderDepositRequest.Code

open Codec
namespace E2eScal.Wit{X}GR

set_option maxRecDepth 100000

def P : Program := [.label "ssz.ErrSize"] ++ {X}Unmarshal

theorem P_len : P.length = {L} := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem hk1 : {X}Unmarshal.IsInfixAt Host.prog 1 := infixAt_of [.label "ssz.ErrSize"] [] (by simp [Host.prog, mkHost, P]) rfl

theorem hf1 : LabelsFresh {X}Unmarshal 1 := labelsFresh_of (by decide)

theorem label_err : label "ssz.ErrSize" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P]) (by simp [labs])

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt

/-- ErrSize word 0 · word 1 · guard (r14 = 0x10000) · saved rbp · return slot (rsp = 0x10020) · spill rax · spill rbx. -/
def block : List UInt8 := w 0x10e8 ++ (w 0x2a ++ (w 0 ++ (z 8 ++ (w 0 ++ (z 8 ++ z 8)))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def cs0 (len : UInt64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10100, 0x10200, len, 0, 0, 0, 0x10020, 0, 0, 0, 0, 0, 0, 0, 0x10000, 0⟩, zmms, flags, mem⟩

def R0 : DataMem → Prop := Eq ((z 8).At (0x10028 : BitVec 64))

set_option maxHeartbeats 4000000 in
/-- **Non-vacuity of the generated `{x}_g5dec_reject`.** -/
theorem {x}_reject_runs (len : UInt64) (hlen : len ≠ {N}) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10e8
        ∧ st.data.regs.rbx = 0x2a)
      ⟨cs0 len zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (E2eScal.Gen.{x}_g5dec_reject 1 hk1 hf1 (cs0 len zmms flags) 0 0 0x10e8 0x2a (z 8) (z 8) rfl rfl R0
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split []
      simp only [cs0, R0, w, ElfData.PrysmTarget.e2eErrSize_addr, label_err, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat,
        Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) hlen)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := {x}_reject_runs {N - 1} (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := {x}_reject_runs {N + 1} (by decide) z' f
example (z' : RegZmms) (f : StatusFlags) := {x}_reject_runs 0 (by decide) z' f

end E2eScal.Wit{X}GR
'''


# ---------------------------------------------------------------- accept witness, callee frame 0x38 (u64 fields only)
def acc38(X, n):
    """SyncAggregatorSelectionData frame (sub $0x38; Slot call first, then in-line u64). nf input words."""
    ty, fs, _ = T[X]
    x = X.lower()
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
    blk = ['w0'] + ins + (['z 8'] if gap else []) + ['z 8'] * (1 + nf) + [f'z {tail_len}'] + \
        ['z 8', 'z 8', 'z 8', 'z 8', 'z 40', 'z 8', 'w0', 'z 8', 'z 8']
    R0 = (f'Eq ((z {tail_len}).At ({hexs(tail)} : BitVec 64)) ⋆ Eq ((z 8).At (0x10070 : BitVec 64))\n'
          '    ⋆ Eq ((z 40).At (0x10080 : BitVec 64))')
    if gap:
        R0 = 'Eq ((z 8).At (0x10018 : BitVec 64)) ⋆ ' + R0
    nlist = 7 + nf
    zs = ' '.join(['(z 8)'] * nlist)
    rfls = ' '.join(['rfl'] * nlist)
    hins = ' '.join(f'(hin{i} : in{i}.length = 8)' for i in range(nf))
    insp = ' '.join(ins)
    hinsn = ' '.join(f'hin{i}' for i in range(nf))
    z8s = ' '.join(['(z 8)'] * nf)
    rr = ' '.join(['rfl'] * nf)
    reps = ' '.join(f'(Int.toBytes 8 {v})' for v in ['0x0123456789abcdef', '7', '0x40'][:nf])
    decs = ' '.join(['(by decide)'] * nf)
    ffs = ' '.join(['(List.replicate 8 0xff)'] * nf)
    return f'''import E2eScal.Gen5F24{X}Dec
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witness of the generated `{x}_g5dec_accept` (`{ty}` decoder accept path; FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of the G5-C witness `WitSaGA.lean`
(frame `0x38`, one Slot callee) with the {ty} host and layout ({nf} input words). It shows that the premises of
the generated accept theorem (statement = kind instance) are satisfiable. Host: one label, the real Go 1.26.10
`(*{ty}).UnmarshalSSZ` (index 1) and `primitives.Slot` UnmarshalSSZ ({1 + n}).
One memory block at `0x10000`: guard · input ({nf} × 8){' · 8 unused' if gap else ''} · receiver (state, {nf} fields,
then the untouched tail) · callee frame-pointer slot (rsp − 80) · callee return slot (rsp − 72) · 8 untouched · callee
rbx spill (rsp − 56) · 40 untouched · saved rbp · return slot (rsp = 0x100b0) · spill rax · spill rbx. The receiver is
at rax = 0x10020 (protoc struct, `prysm/ir/ir-mainnet.json` gc amd64 layout: `state` 0, fields at 8 …). The frame
`R` is the untouched receiver tail and frame ranges. For every {N}-byte input every premise holds and the decoder
returns nil. The receiver is a Go value of `{ty}` (all zero).
-/

open Machine Runtime Machine.Witness E2eScal Codec Prysm.BuilderDepositRequest.Code

namespace E2eScal.Wit{X}GA

set_option maxRecDepth 100000

def P : Program := [.label "pad0"] ++ {X}Unmarshal ++ Prysm.Slot.Code.unmarshalSSZ

theorem P_len : P.length = {plen} := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk1 : {X}Unmarshal.IsInfixAt Host.prog 1 :=
  infixAt_of [.label "pad0"] (Prysm.Slot.Code.unmarshalSSZ) (by simp [prog_eq, P, List.append_assoc]) rfl
theorem hf1 : LabelsFresh {X}Unmarshal 1 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hk{1 + n} : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog {1 + n} :=
  infixAt_of ([.label "pad0"] ++ {X}Unmarshal) ([])
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hf{1 + n} : LabelsFresh Prysm.Slot.Code.unmarshalSSZ {1 + n} := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block ({insp} : List UInt8) : List UInt8 :=
  {nest(blk)}

def mem ({insp} : List UInt8) : DataMem := (block {insp}).At (0x10000 : BitVec 64)

def cs0 ({insp} : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10020, 0x10008, {N}, 0, 0, {N}, 0x100b0, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem {insp}⟩

/-- The frame of the witness: unused bytes, the receiver tail and the untouched frame ranges. -/
def R0 : DataMem → Prop :=
  {R0}

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `{x}_g5dec_accept`** (premises of the kind instance). -/
theorem {x}_accept_runs ({insp} : List UInt8) {hins}
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 {insp} zmms flags, Host.addrOf 1⟩ :=
  eventually_mono (E2eScal.Gen.{x}_g5dec_accept 1 hk1 hf1 {1 + n} hk{1 + n} hf{1 + n}
    {insp} {hinsn} (cs0 {insp} zmms flags)
    0 0 {zs}
    {rfls}
    R0
    (by
      have H : Eq ((block {insp}).At (0x10000 : BitVec 64)) (mem {insp}) := rfl
      wit_split [{', '.join(f'hin{i}' for i in range(nf))}]
      simp only [cs0, R0, w0, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [cs0]) rfl)
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input; a representative input; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) := {x}_accept_runs {z8s} {rr} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  {x}_accept_runs {reps} {decs} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  {x}_accept_runs {ffs} {rr} z' f

end E2eScal.Wit{X}GA
'''


# ---------------------------------------------------------------- accept witness, byte fields (+ callees)
def accbytes(X, n, frame):
    """frame '20': Deposit_Data frame (sub $0x20, no call; S = 16); 'pd': slices + callees (S = 8), frame F."""
    ty, fs, _ = T[X]
    x = X.lower()
    N = sum(f[2] for f in fs)
    heap = sum(f[2] for f in fs if f[1] == 'b')
    nb = sum(1 for f in fs if f[1] == 'b')
    gsize = {'Dpr': 128, 'Bdr': 120, 'Pdc': 72, 'Vid': 80}[X]
    callees = {'Dpr': [], 'Bdr': [], 'Pdc': ['Sl'], 'Vid': ['Vi', 'Ep']}[X]
    ins = [f'f{i}' for i in range(len(fs))]
    ops = [f'oP{j + 1}' for j in range(nb)]
    params = ins + ops
    # addresses
    guard = 0x1000c + heap
    rbx = guard + 8
    rax = rbx + N
    # receiver words (state at 0; per field: u64 word or (ptr, len, cap))
    rwords, rnames = ['z 8'], []
    j = 0
    for f in fs:
        if f[1] == 'u':
            rwords.append('z 8')
            rnames.append('(z 8)')
        else:
            rwords += [ops[j], 'z 8', 'z 8']
            rnames += [ops[j], '(z 8)', '(z 8)']
            j += 1
    rlen = 8 * len(rwords)
    tail = gsize - rlen
    assert tail == 32, (X, tail)
    endr = rax + gsize
    if frame == '20':
        S = 16
        F_lo = endr                      # lo (S bytes) = rsp - 48 - S
        rsp = F_lo + 48 + S
        # lo 16 · rslot · spl 24 · l18 · fp · ret · s1 · s2 · caller word
        stack = ['z 16', 'z 8', 'z 24', 'z 8', 'z 8', 'w0', 'z 8', 'z 8', 'z 8']
        R0 = f'Eq ((z 32).At ({hexs(rax + rlen)} : BitVec 64)) ⋆ Eq ((z 8).At ({hexs(rsp + 24)} : BitVec 64))'
        lists = ['(z 8)', '(z 8)', '(z 8)', '(z 24)', '(z 8)', '(z 8)', '(z 16)', '(z 8)'] + rnames
        lens = ['rfl'] * 7
        Sarg = '16 rfl'
        callargs = ''
    else:
        S = 8
        Fr = {'Pdc': 0x40, 'Vid': 0x50}[X]
        rslot_off = Fr + 16              # return slot at rsp - (F + 16)
        F_lo = endr
        rsp = F_lo + rslot_off + 8 + S   # lo (S + 8) at rsp - rslot_off - 8 - S
        lsave = {'Pdc': 32, 'Vid': 48}[X]
        # rsp - rslot_off - 8 - S: lo (16) · rslot · sp0 sp1 sp2 · gap1 · l28 · gap2 · fp · ret · s1 · s2 · unused · s4
        sp0 = rsp - rslot_off + 8        # = rsp - (F + 8)
        gap1 = sp0 + 24
        gap1_len = (rsp - lsave) - gap1
        gap2 = rsp - lsave + 8
        gap2_len = (rsp - 8) - gap2
        stack = ['z 16', 'z 8', 'z 8', 'z 8', 'z 8', f'z {gap1_len}', 'z 8', f'z {gap2_len}', 'z 8', 'w0', 'z 8', 'z 8',
                 'z 8', 'z 8']
        R0 = (f'Eq ((z 32).At ({hexs(rax + rlen)} : BitVec 64)) ⋆ Eq ((z {gap1_len}).At ({hexs(gap1)} : BitVec 64))'
              f' ⋆ Eq ((z {gap2_len}).At ({hexs(gap2)} : BitVec 64))\n    ⋆ Eq ((z 8).At ({hexs(rsp + 24)} : BitVec 64))')
        lists = ['(z 8)'] * 9 + ['(z 16)', '(z 8)'] + rnames
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
    blk = ['Int.toBytes 8 (0x1000c : BitVec 64).toInt', '[0, 0, 0, 0]', f'z {heap}', 'w0'] + ins + rwords + ['z 32'] + stack
    blk = [b if b in params or b in ('w0',) else f'({b})' for b in blk]
    # program
    b0 = 9 + n
    idx, prog, hks = b0, f'dataLabels ++ {X}Unmarshal', []
    cl = [CALLEE[c][0] for c in callees]
    tailp = cl + ['BumpAlloc1', 'RtCopy']
    calls = []
    for c in cl:
        rest = ' ++ '.join(tailp[tailp.index(c) + 1:]) or '[]'
        hks.append(f'theorem hk{idx} : {c}.IsInfixAt Host.prog {idx} :=\n  infixAt_of ({prog}) ({rest})\n'
                   f'    (by simp [prog_eq, P, List.append_assoc]) (by rfl)\n'
                   f'theorem hf{idx} : LabelsFresh {c} {idx} := labelsFresh_of (by rw [prog_eq]; decide)')
        calls.append(f'{idx} hk{idx} hf{idx}')
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
        return f'(z {f[2]})'

    def rep(i, f):
        if f[1] == 'u':
            return f'(Int.toBytes 8 0x0123456789abcde{i})'
        return f'((List.range {f[2]}).map (fun i => UInt8.ofNat (i + {10 * i})))'
    ex0 = ' '.join([zero(f) for f in fs] + ['(z 8)'] * nb + ['rfl'] * (len(fs) + nb))
    ex1 = ' '.join([rep(i, f) for i, f in enumerate(fs)] + [f'(Int.toBytes 8 0x{2 + j}0000)' for j in range(nb)]
                   + [('(by decide)' if f[1] == 'u' else 'rfl') for f in fs] + ['(by decide)'] * nb)
    ex2 = ' '.join([f'(List.replicate {f[2]} 0xff)' for f in fs] + ['(List.replicate 8 0xff)'] * nb
                   + ['rfl'] * (len(fs) + nb))
    opens = 'Machine Runtime Machine.Witness E2eScal Codec Prysm.BuilderDepositRequest.Code'
    cdoc = ', '.join(f'`{CALLEE[c][1]}` UnmarshalSSZ' for c in callees)
    return f'''import E2eScal.Gen5F24{X}Dec
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost

/-!
# Witness of the generated `{x}_g5dec_accept` (`{ty}` decoder accept path; FLAT24 / H7)

Written by the FLAT24 evaluator with its evidence script `f24wit.py`: the text of `{'WitDdA.lean' if frame == '20' else 'WitPdA.lean'}` with the
{ty} host and layout. It shows that the premises of the generated accept theorem (statement = kind instance)
are satisfiable. Host: data labels, the real Go 1.26.10 `(*{ty}).UnmarshalSSZ` (index 9){', ' + cdoc if cdoc else ''},
the 1-byte bump `runtime.makeslice` ({bi}, `bump_makeslice1`) and `RtCopy` ({ri}, `rt_memmove`).
One memory block at `0x10000`: bump pointer, writeBarrier word, the {heap}-byte heap, guard word, the {N} input bytes,
the {gsize}-byte receiver (`prysm/ir/ir-mainnet.json` gc amd64 layout: `state`, per byte field a slice header with an
old pointer word and len = cap = 0, per uint64 field a zero word, then 32 untouched tail bytes), the callee block
(`S = {S}`), the return slot, the argument area, the untouched frame ranges, the slice pointer save, the saved rbp
and the caller's slots (rsp = {hexs(rsp)}). The frame `R` is the receiver tail, the untouched frame ranges and the
caller's word at rsp + 24. For every input and every old pointer word every premise holds and the decoder returns
nil. The receiver is a Go value of `{ty}` (zero `state`, zero-length slices, zero integers).
-/

open {opens}

namespace E2eScal.Wit{X}GA

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.fvBump", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def P : Program := {prog} ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = {plen} := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk9 : {X}Unmarshal.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels ({' ++ '.join(tailp)}) (by simp [prog_eq, P, List.append_assoc]) rfl
{chr(10).join(hks)}
theorem hk{bi} : BumpAlloc1.IsInfixAt Host.prog {bi} :=
  infixAt_of ({prog}) RtCopy
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)
theorem hk{ri} : RtCopy.IsInfixAt Host.prog {ri} :=
  infixAt_of ({prog} ++ BumpAlloc1) []
    (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf9 : LabelsFresh {X}Unmarshal 9 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf{ri} : LabelsFresh RtCopy {ri} := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf{bi} : ∀ i < {bi}, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_wb : label "runtime.writeBarrier" = 0x10008 :=
  mk_label P _ 8 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
abbrev w0 : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt

def block ({pp} : List UInt8) : List UInt8 :=
  {nest(blk)}

def mem ({pp} : List UInt8) : DataMem :=
  (block {pp}).At (0x10000 : BitVec 64)

def cs0 ({pp} : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨{hexs(rax)}, {hexs(rbx)}, {N}, 0, 0, {N}, {hexs(rsp)}, 0, 0, 0, 0, 0, 0, 0, {hexs(guard - 16)}, 0⟩, zmms, flags,
    mem {pp}⟩

/-- The frame of the witness. -/
def R0 : DataMem → Prop :=
  {R0}

theorem lift_heap {{X : DataMem → Prop}} {{m : DataMem}}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((z {heap}).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap {heap} ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of the generated `{x}_g5dec_accept`** (premises of the kind instance are satisfiable). -/
theorem {x}_accept_runs ({pp} : List UInt8) {hparams}
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 {pp} zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (E2eScal.Gen.{x}_g5dec_accept 9 hk9 hf9 {' '.join(calls)}
    {' '.join(ins)} {hin} (cs0 {pp} zmms flags)
    0 0 {' '.join(lists)}
    {' '.join(lens + lens2)}
    R0 {Sarg} bumpHeap {heap}
    (by
      have H : Eq ((block {pp}).At (0x10000 : BitVec 64)) (mem {pp}) := rfl
      wit_split [{wl}]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((z {heap}).At _))] at H
      have H2 := lift_heap H
      simp only [cs0, R0, w0, label_wb, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [cs0]) rfl (Nat.le_refl _) (bump_makeslice1 {bi} hk{bi} hf{bi} _) (rt_memmove {ri} hk{ri} hf{ri} _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- Zero input with nil slices; a representative input with non-nil old pointer words; all-0xff input. -/
example (z' : RegZmms) (f : StatusFlags) :=
  {x}_accept_runs {ex0} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  {x}_accept_runs {ex1} z' f
example (z' : RegZmms) (f : StatusFlags) :=
  {x}_accept_runs {ex2} z' f

end E2eScal.Wit{X}GA
'''


if __name__ == '__main__':
    kr = sys.argv[1]
    which = sys.argv[2:] or ['Dpr', 'Bdr', 'Bbr', 'Bsr', 'Epr', 'Pdc', 'Vid']
    for X in which:
        n = slen(kr, X)
        d = os.path.join(kr, 'lean', 'Prysm', GO_TYPE[X])
        open(os.path.join(d, 'WitnessGeneratedDecodeRejectSize.lean'), 'w').write(new_names(reject(X, n), X))
        if X in ('Bbr', 'Bsr', 'Epr'):
            a = acc38(X, n)
        elif X in ('Dpr', 'Bdr'):
            a = accbytes(X, n, '20')
        else:
            a = accbytes(X, n, 'pd')
        open(os.path.join(d, 'WitnessGeneratedDecodeAccept.lean'), 'w').write(new_names(a, X))
        print(X, n)
