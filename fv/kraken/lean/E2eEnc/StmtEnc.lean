import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import E2eEnc.Code
import E2eEnc.Defs

/-!
# Hand STATEMENTS of the encoder target `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (statements only)

Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Statement shape: `Prysm/Checkpoint/EncodeFastPath.lean`, `Prysm/Checkpoint/EncodeGrowFirstSite.lean`, `Prysm/Checkpoint/EncodeSpec.lean` (Checkpoint encoder) and
`Prysm/IndexedAttestation/Statements.lean` (exact caller frame `R`, contracts as hypotheses, receiver and input kept).

    func (c *DataColumnsByRootIdentifier) MarshalSSZTo(dst []byte) ([]byte, error) {   // fulu.ssz.go:1754
        if len(c.BlockRoot) != 32 { return nil, ssz.ErrBytesLength }                     // bytes-length reject
        dst = append(dst, c.BlockRoot...)                                                // site 1 (growslice 23)
        dst = ssz.WriteOffset(dst, 36)                                                   // site 2 (growslice 49)
        if len(c.Columns) > 128 { return nil, ssz.ErrListTooBig }                        // too-big reject
        for _, o := range c.Columns { dst = binary.LittleEndian.AppendUint64(dst, o) }   // site 3 (growslice 94)
        return dst, err }

Arguments: rax = c, rbx = dst.ptr, rcx = len(dst), rdi = cap(dst). Result: rax, rbx, rcx = the slice, rdi, rsi = the
error (itab word, data word).
Receiver (IR `go_fields`, size 88): `state` 0, `BlockRoot` 8 (ptr, len, cap), `Columns` 32 (ptr, len, cap),
`unknownFields` 56, `sizeCache` 80. The code reads c + 8, c + 16, c + 32, c + 40 only; the rest is in `R`.
Frame (x = entry rsp): guard `lea -0x8(%rsp),%r12; cmp 0x10(%r14),%r12; jbe` (so `guard + 8 < x`); `push %rbp`
(x − 8); `add $-0x80` (rsp = x − 136). Spills: x + 8 (rax, directive 12), x + 16 (rbx, directive 8), x + 24 (rcx,
directive 16, grow site 1 only). Locals: x − 16 (root pointer, grow site 1 only), x − 24 (Columns pointer), x − 32
(dst pointer), x − 40 (n), x − 48 (i, grow site 3 only), x − 56 (cap), x − 64 (len + 32), x − 72 (word, grow site 3
only). Callee spill area: x − 136 (40 bytes, growslice). Runtime call return slot x − 144; scratch `S` below it.
-/

open Machine Runtime TestTarget EthLib.Serialization.Ssz E2eEnc.Code
variable [Host]

namespace E2eEnc

/-- **Fast path, capacity sufficient (machine).** `len(BlockRoot) = 32`, `n = len(Columns) ≤ 128` and
`len + 36 + 8n ≤ cap`: no growslice site is taken; the encoder writes `root ‖ offset 36 ‖ cb` at `dst.ptr + len`
(the 36 + 8n bytes `d` are overwritten) and returns `(dst.ptr, len + 36 + 8n, cap, nil)`. The receiver words, the
root and column bytes, the guard word and the caller's frame `R` are unchanged; the spill slots hold rax and rbx. -/
def dc_marshal_fast_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (n : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (root cb pre d : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8 * n)
    (hpre : pre.length = s.regs.rcx.toNat) (hd : d.length = 36 + 8 * n)
    (fp s1 s2 l24 l32 l40 l56 l64 rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl56 : l56.length = 8) (hl64 : l64.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 + 8 * n ≤ s.regs.rdi.toNat)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36 + 8 * n ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l24' l32' l40' l56' l64' rslot' scr : List UInt8), l24'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8
          ∧ l56'.length = 8 ∧ l64'.length = 8 ∧ rslot'.length = 8 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l24'.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l64'.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
          ⋆ Eq ((pre ++ root ++ dcOff ++ cb).At s.regs.rbx.toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **First-site grow path: one grow at site 1 only (machine).** `len ≤ cap < len + 32`: `append(dst, BlockRoot...)` calls
`growslice(dst.ptr, len + 32, cap, 32, uint8)` (contract `GrowsliceC Heap e2eU8Type_addr 1 S`). The premise
`len + 36 + 8n ≤ nextSliceCap (len + 32) cap` makes the new capacity enough for sites 2 and 3, so they do not grow.
The encoder returns `(new, len + 36 + 8n, newCap, nil)`; the new block starts with `pre ‖ root ‖ offset 36 ‖ cb`
(the rest `rest` is named); the old block `pre` is unchanged; the heap shrinks by `newCap`. -/
def dc_marshal_grow_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (n : Nat) (hnb : nb.toNat = n) (hn : n ≤ 128)
    (root cb pre : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8 * n)
    (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 32)
    (hfit : s.regs.rcx.toNat + 36 + 8 * n ≤ nextSliceCap (s.regs.rcx.toNat + 32) s.regs.rdi.toNat)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 32) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 36 + 8 * n
        ∧ nextSliceCap (s.regs.rcx.toNat + 32) s.regs.rdi.toNat ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l16' l24' l32' l40' l56' l64' spl' rslot' scr rest : List UInt8) (av' : Nat), l16'.length = 8
          ∧ l24'.length = 8 ∧ l32'.length = 8 ∧ l40'.length = 8 ∧ l56'.length = 8 ∧ l64'.length = 8
          ∧ spl'.length = 40 ∧ rslot'.length = 8 ∧ scr.length = S
          ∧ s.regs.rcx.toNat + 36 + 8 * n + rest.length = st.data.regs.rcx.toNat
          ∧ av' + st.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rcx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (l16'.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (l24'.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l40'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l64'.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 136))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (root.At pr) ⋆ Eq (cb.At pc)
          ⋆ Eq (pre.At s.regs.rbx.toBitVec)
          ⋆ Eq ((pre ++ root ++ dcOff ++ cb ++ rest).At st.data.regs.rax.toBitVec)
          ⋆ Heap av' ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Bytes-length reject: BlockRoot length (machine).** `len(BlockRoot) = bl ≠ 32`: the encoder returns
`(nil, 0, 0, ssz.ErrBytesLength)` (the two words `e0`, `e1` of the global); only the saved rbp and the rbx spill slot
change. -/
def dc_reject_bytes_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (pr bl : BitVec 64) (hbl : bl ≠ 32)
    (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 bl.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 bl.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrBytesLength_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrBytesLength" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Too-big reject: Columns too long (machine).** `len(BlockRoot) = 32`, `len + 36 ≤ cap` (sites 1 and 2 do not grow) and
`128 < n < 2^63` (Go's `len > 128`, signed `jg`): the encoder has written `root ‖ offset 36` at `dst.ptr + len` and
returns `(nil, 0, 0, ssz.ErrListTooBig)`. The column bytes are not read. -/
def dc_reject_toobig_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (pr nb : BitVec 64) (hn1 : 128 < nb.toNat) (hn2 : nb.toNat < 2 ^ 63)
    (root pre d : List UInt8) (hroot : root.length = 32)
    (hpre : pre.length = s.regs.rcx.toNat) (hd : d.length = 36)
    (fp s1 s2 l32 l56 l64 rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (hl32 : l32.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8)
    (hrs : rslot.length = 8) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (root.At pr)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrListTooBig").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 ≤ s.regs.rdi.toNat)
    (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rcx = 0 ∧ st.data.regs.rdi = e0 ∧ st.data.regs.rsi = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (l32' l56' l64' rslot' scr : List UInt8), l32'.length = 8 ∧ l56'.length = 8 ∧ l64'.length = 8
          ∧ rslot'.length = 8 ∧ scr.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l32'.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l56'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq (l64'.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (rslot'.At (s.regs.rsp.toBitVec - 144))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq (root.At pr)
          ⋆ Eq ((pre ++ root ++ dcOff).At s.regs.rbx.toBitVec)
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrListTooBig").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrListTooBig" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Fast path against EthLib (spec companion, shape of `Prysm.Checkpoint.Encode.fast_path_spec`).** For a receiver holding the Go
layout of `g : PDc` (BlockRoot bytes `g.root`, Columns backing bytes `u64Bytes g.cols`), the fast path returns
`len + |bs|` and `dst[0 : len + |bs|] = pre ‖ bs`, where `bs = serialize prysmDcDesc g.toValue`. The full frame
accounting is `dc_marshal_fast_stmt`. -/
def dc_marshal_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (g : PDc) (hnb : nb.toNat = g.cols.length)
    (pre d : List UInt8) (hpre : pre.length = s.regs.rcx.toNat) (hd : d.length = 36 + 8 * g.cols.length)
    (fp s1 s2 l24 l32 l40 l56 l64 rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (hl24 : l24.length = 8) (hl32 : l32.length = 8) (hl40 : l40.length = 8)
    (hl56 : l56.length = 8) (hl64 : l64.length = 8) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (g.root.toList.At pr) ⋆ Eq ((Spec.u64Bytes g.cols).toList.At pc)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 36 + 8 * g.cols.length ≤ s.regs.rdi.toNat)
    (hmm : MemmoveC S),
    ∃ bs, serialize prysmDcDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + bs.size ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq ((pre ++ bs.toList).At s.regs.rbx.toBitVec) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **First-site grow path against EthLib.** The grow path at site 1 returns `len + |bs|` with `len + |bs| ≤ newCap`, and the new block
starts with `pre ‖ bs`, where `bs = serialize prysmDcDesc g.toValue`. The full accounting is `dc_marshal_grow_stmt`. -/
def dc_marshal_grow_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : DcMarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DcMarshal k)
    (s : MachineData) (ra guard : UInt64) (pr pc nb : BitVec 64) (g : PDc) (hnb : nb.toNat = g.cols.length)
    (pre : List UInt8) (hpre : pre.length = s.regs.rcx.toNat)
    (fp s1 s2 s3 l16 l24 l32 l40 l56 l64 spl rslot : List UInt8) (hfp : fp.length = 8) (h1 : s1.length = 8)
    (h2 : s2.length = 8) (h3 : s3.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl56 : l56.length = 8) (hl64 : l64.length = 8)
    (hspl : spl.length = 40) (hrs : rslot.length = 8)
    (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pr.toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 pc.toInt).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq ((Int.toBytes 8 nb.toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (g.root.toList.At pr) ⋆ Eq ((Spec.u64Bytes g.cols).toList.At pc)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Heap avail ⋆ R)
    (hguard : guard.toNat + 8 < s.regs.rsp.toNat)
    (hlc : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hgrow : s.regs.rdi.toNat < s.regs.rcx.toNat + 32)
    (hfit : s.regs.rcx.toNat + 36 + 8 * g.cols.length ≤ nextSliceCap (s.regs.rcx.toNat + 32) s.regs.rdi.toNat)
    (hbud : 2 * nextSliceCap (s.regs.rcx.toNat + 32) s.regs.rdi.toNat + 8192 ≤ avail) (hmax : avail ≤ maxAlloc)
    (hgs : GrowsliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
    ∃ bs, serialize prysmDcDesc g.toValue = .ok bs ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + bs.size ∧ s.regs.rcx.toNat + bs.size ≤ st.data.regs.rcx.toNat
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((pre ++ bs.toList).At st.data.regs.rax.toBitVec)
          ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Bytes-length reject against EthLib.** EthLib refuses a BlockRoot of any length other than 32. -/
def dc_spec_reject_bytes_stmt : Prop :=
  ∀ (r : Array UInt8) (cols : List UInt64), r.size ≠ 32 → ∃ e, serialize prysmDcDesc (dcValue r cols) = .error e

/-- **Too-big reject against EthLib.** EthLib refuses more than 128 columns. -/
def dc_spec_reject_toobig_stmt : Prop :=
  ∀ (r : Vector UInt8 32) (cols : List UInt64), 128 < cols.length →
    ∃ e, serialize prysmDcDesc (dcValue r.toArray cols) = .error e

end E2eEnc
