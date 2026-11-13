import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Machine.Labels
import Prysm.ElfData.CheckpointAndEpoch
import Prysm.ElfData.SyncAggregateAndSyncCommittee
import Prysm.HistoricalBatch.Code
import Prysm.HistoricalBatch.SpecDefinitions

/-!
# Hand STATEMENTS of the target `(*v1alpha1.HistoricalBatch).UnmarshalSSZ` (statements only, no proof)

Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Statement shape: `Prysm.SyncCommittee.Statements` with two 8192-element `[][]byte` fields and no tail field.

    func (c *HistoricalBatch) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 524288 { return ssz.ErrSize }
        c.BlockRoots = make([][]byte, 8192)
        for i := 0; i < 8192; i++ {
            tmp := make([]byte, 0, 32); tmp = append(tmp, buf[i*32:(1+i)*32]...); c.BlockRoots[i] = tmp }
        c.StateRoots = make([][]byte, 8192)
        for i := 0; i < 8192; i++ {
            tmp := make([]byte, 0, 32); tmp = append(tmp, buf[262144+i*32:262144+(1+i)*32]...); c.StateRoots[i] = tmp }
        return err }

Receiver: native struct, IR `go_fields` (`prysm/ir/ir-mainnet.json`, size 48): `BlockRoots` 0 (ptr, len, cap),
`StateRoots` 24 (ptr, len, cap). There is no `state`, `unknownFields` or `sizeCache` field (SyncCommittee had them).
The loops read `BlockRoots.len` / `StateRoots.len` (bounds checks, directives 65, 134) and the backing array
pointer (70, 140) from the receiver in every iteration.

Frame (`.S`, x = entry rsp): `sub $0x38`; `0x48(%rsp)` = x + 8 (rax spill), `0x50(%rsp)` = x + 16 (rbx spill,
also written at directive 7 before the size check); loop locals `0x18(%rsp)` = x − 40 (i + 1), `0x20(%rsp)` = x − 32
(32i), `0x28(%rsp)` = x − 24 (i), `0x30(%rsp)` = x − 16 (element pointer); `0x0…0x17(%rsp)` = x − 64 (24 bytes,
`spl`, makeslice's spill area); runtime call return slot x − 72; `lo` = the `S` scratch bytes below it.
Calls: makeslice of each backing array (`ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr`, esz 24, len = cap = 8192; the same type
word as SyncCommittee, asserted by `gen/e2e/hblink.py data`), 2 × 8192 uint8 makeslice (len 0, cap 32) + memmove (32) pairs.
Heap: 2 · (24·8192 + 32·8192) = 917504 bytes. The last runtime call is the memmove at directive 132, so the
return slot holds directive 133 at the end. The four loop locals are dead after the loops; the postcondition owns
them with unnamed 8-byte values.
`runtime.panicBounds` (directives 161, 164, 166, 168) is class (a): the bounds checks are to be proved not taken.
Size reject: directives 2–10, `cmp $0x80000,%rcx; jne L_7b` taken, 30–35.
-/

open Machine Runtime EthLib.Serialization.Ssz Prysm.HistoricalBatch.Code
variable [Host]

namespace Prysm.HistoricalBatch

/-- **Accept (machine).** On a 524288-byte input `brs.flatten ++ srs.flatten` (2 × 8192 blocks of 32 bytes)
the decoder returns nil; the receiver holds two fresh `[][]byte` of len = cap = 8192 whose backing arrays at `A1`,
`A2` have the headers `(ps1[i], 32, 32)`, `(ps2[i], 32, 32)` and whose elements equal `brs[i]`, `srs[i]`; the
input, the spills, the caller's frame `R` and the stack guard are unchanged; 917504 heap bytes are used. -/
def Decode.accept_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (brs srs : List (List UInt8)) (hbrs : brs.length = 8192) (hbr : ∀ e ∈ brs, e.length = 32)
    (hsrs : srs.length = 8192) (hsr : ∀ e ∈ srs, e.length = 32)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl18 : l18.length = 8) (hl20 : l20.length = 8) (hl28 : l28.length = 8) (hl30 : l30.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 72 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (brs.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (srs.flatten.At (s.regs.rbx.toBitVec + 262144))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 524288) (hav : 917504 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S)
    (hmsA : MakesliceC Heap ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr 24 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A1 A2 : BitVec 64) (ps1 ps2 : List (BitVec 64)) (l18' l20' l28' l30' spl' lo' : List UInt8),
          ps1.length = 8192 ∧ ps2.length = 8192 ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ l28'.length = 8
          ∧ l30'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l18'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l20'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l30'.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 133)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 72 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 917504)
          ⋆ Eq (brs.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (srs.flatten.At (s.regs.rbx.toBitVec + 262144))
          ⋆ Eq ((Int.toBytes 8 A1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 A2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps1).At A1) ⋆ Prysm.SyncCommittee.elementBlocks ps1 brs ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps2).At A2) ⋆ Prysm.SyncCommittee.elementBlocks ps2 srs
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Size reject (machine).** `len(buf) ≠ 524288`: the decoder returns the two words `e0`, `e1` of
`ssz.ErrSize`; the rbx spill slot holds rbx, the caller's frame `R` (the receiver and the input included) and
the global are unchanged. -/
def Decode.reject_size_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 524288),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (spec).** If EthLib accepts `bsA` against `desc` as `v`, there is `g : SszValue` with
`g.toValue = v` and `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the
receiver holds `g` (postcondition of `Decode.accept_statement` with `brs = g.brs`, `srs = g.srs`). -/
def Decode.accept_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l18 l20 l28 l30 spl rslot lo aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl18 : l18.length = 8) (hl20 : l20.length = 8) (hl28 : l28.length = 8) (hl30 : l30.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 72 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.brs.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (g.srs.flatten.At (s.regs.rbx.toBitVec + 262144))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 917504 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S)
    (hmsA : MakesliceC Heap ElfData.SyncAggregateAndSyncCommittee.lvSliceType_addr 24 S) (hmm : MemmoveC S),
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A1 A2 : BitVec 64) (ps1 ps2 : List (BitVec 64)) (l18' l20' l28' l30' spl' lo' : List UInt8),
          ps1.length = 8192 ∧ ps2.length = 8192 ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ l28'.length = 8
          ∧ l30'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l18'.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l20'.At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq (l28'.At (s.regs.rsp.toBitVec - 24)) ⋆ Eq (l30'.At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 133)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 72 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 917504)
          ⋆ Eq (g.brs.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (g.srs.flatten.At (s.regs.rbx.toBitVec + 262144))
          ⋆ Eq ((Int.toBytes 8 A1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 A2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 8192).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps1).At A1) ⋆ Prysm.SyncCommittee.elementBlocks ps1 g.brs ⋆ Eq ((Prysm.SyncCommittee.sliceHeaders 32 ps2).At A2) ⋆ Prysm.SyncCommittee.elementBlocks ps2 g.srs
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Size reject (spec).** `bs.size ≠ 524288`: EthLib rejects, and the machine code returns the two words of
`ssz.ErrSize` (postcondition of `Decode.reject_size_statement`). -/
def Decode.reject_size_spec_statement : Prop :=
  ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (bs : Array UInt8) (hbs : bs.size ≠ 524288)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Reject completeness (spec).** Every input that EthLib rejects has `size ≠ 524288`: the path condition of
the decoder's one reject site (`runtime.panicBounds` is not an error return; it is to be proved unreachable). -/
def Decode.reject_complete_statement : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize desc bs = .ok v) → bs.size ≠ 524288

end Prysm.HistoricalBatch
