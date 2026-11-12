import Fk.Contracts
import Fk.Frame
import Fk.Bytes
import Fk.Labels
import E2e.Data
import E2eList.Code
import E2eList.Data
import E2eList.Defs

/-!
# Hand STATEMENTS of the target `(*v1alpha1.SyncCommittee).UnmarshalSSZ` (statements only, no proof)

Frozen at their commit. A later change needs a new name and a reason; these definitions stay.
Statement shape: as `StmtSa.lean` (`E2eScal.H4.dd_accept_stmt` and its spec companions), with a 512-element
`[][]byte` field.

    func (c *SyncCommittee) UnmarshalSSZ(buf []byte) error {
        if uint64(len(buf)) != 24624 { return ssz.ErrSize }
        c.Pubkeys = make([][]byte, 512)
        for i := 0; i < 512; i++ {
            tmp := make([]byte, 0, 48); tmp = append(tmp, buf[i*48:(1+i)*48]...); c.Pubkeys[i] = tmp }
        c.AggregatePubkey = make([]byte, 0, 48)
        c.AggregatePubkey = append(c.AggregatePubkey, buf[24576:24624]...)
        return err }

Receiver: protoc struct, IR `go_fields` (`prysm/ir/ir-mainnet.json`, size 88): `state` 0 (8), `Pubkeys` 8
(ptr, len, cap of the `[][]byte`), `AggregatePubkey` 32 (ptr, len, cap), `unknownFields` 56 (24), `sizeCache`
80 (4) (the last two and the padding in `R`). The decoder does not read `state`; the statement keeps it as
`ast`, unchanged. The loop reads `Pubkeys.len` (bounds check, directive 59) and `Pubkeys.ptr` (directive 64)
from the receiver in every iteration.

Frame (`.S`, x = entry rsp): `sub $0x30`; `0x40(%rsp)` = x + 8 (rax spill), `0x48(%rsp)` = x + 16 (rbx spill,
also written at directive 7 before the size check); loop locals `0x18(%rsp)` = x − 32 (i), `0x20(%rsp)` = x − 24
(3i), `0x28(%rsp)` = x − 16 (element pointer, then the AggregatePubkey pointer); `0x0…0x17(%rsp)` = x − 56
(24 bytes, `spl`, makeslice's spill area); runtime call return slot x − 64; `lo` = the `S` scratch bytes below
it. Calls: one makeslice of the backing array (`E2eList.Data.lvSliceType_addr`, esz 24, len = cap = 512), 512
uint8 makeslice (len 0, cap 48) + memmove (48) pairs in the loop, one uint8 makeslice + memmove for
AggregatePubkey. Heap: 24·512 + 48·512 + 48 = 36912 bytes. The last runtime call is the memmove at directive
100, so the return slot holds directive 101 at the end. The two loop locals x − 32 and x − 24 are dead after
the loop; the postcondition owns them with unnamed 8-byte values (`l18'`, `l20'`).
`runtime.panicBounds` (directive 124) is class (a): the bounds check is to be proved not taken.
Size reject: directives 2–10, `cmp $0x6030,%rcx; jne L_7d` taken, 30–35.
-/

open Fk E2e EthLib.Serialization.Ssz E2eList.Code
variable [Host]

namespace E2eList

/-- **Accept (machine).** On a 24624-byte input `pks.flatten ++ agg` (512 blocks of 48 bytes, then 48 bytes)
the decoder returns nil; the receiver holds a fresh `[][]byte` Pubkeys of len = cap = 512 whose backing array
at `A` has the headers `(ps[i], 48, 48)` and whose element i at `ps[i]` equals `pks[i]`, and a fresh
AggregatePubkey (48, len = cap) equal to `agg`; input, `state`, the spills, the caller's frame `R` and the stack
guard are unchanged; 36912 heap bytes are used. -/
def sc_accept_stmt : Prop :=
  ∀ (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (pks : List (List UInt8)) (agg : List UInt8) (hpks : pks.length = 512) (hpk : ∀ e ∈ pks, e.length = 48)
    (hagg : agg.length = 48)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl18 : l18.length = 8) (hl20 : l20.length = 8) (hl28 : l28.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 64 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (pks.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (agg.At (s.regs.rbx.toBitVec + 24576))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = 24624) (hav : 36912 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S)
    (hmsA : MakesliceC Heap E2eList.Data.lvSliceType_addr 24 S) (hmm : MemmoveC S),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A pA : BitVec 64) (ps : List (BitVec 64)) (l18' l20' spl' lo' : List UInt8),
          ps.length = 512 ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l18'.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l20'.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 pA.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 101)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 64 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 36912)
          ⋆ Eq (pks.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (agg.At (s.regs.rbx.toBitVec + 24576))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 512).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 512).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 pA.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((lvHdrs 48 ps).At A) ⋆ lvElems ps pks ⋆ Eq (agg.At pA)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Size reject (machine).** `len(buf) ≠ 24624`: the decoder returns the two words `e0`, `e1` of
`ssz.ErrSize`; the rbx spill slot holds rbx, the caller's frame `R` (the receiver and the input included) and
the global are unchanged. -/
def sc_reject_size_stmt : Prop :=
  ∀ (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 24624),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Accept (spec).** If EthLib accepts `bsA` against `prysmScDesc` as `v`, there is `g : PSc` with
`g.toValue = v` and `bsA = pscEnc g`; with the input chunks of that `g` the machine code returns nil and the
receiver holds `g` (postcondition of `sc_accept_stmt` with `pks = g.pks`, `agg = g.aggregatePubkey`). -/
def sc_accept_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmScDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l18 l20 l28 spl rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hl18 : l18.length = 8) (hl20 : l20.length = 8) (hl28 : l28.length = 8)
    (hspl : spl.length = 24) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PSc, bsA = pscEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 64 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.pks.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (g.aggregatePubkey.toList.At (s.regs.rbx.toBitVec + 24576))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 36912 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S)
    (hmsA : MakesliceC Heap E2eList.Data.lvSliceType_addr 24 S) (hmm : MemmoveC S),
    ∃ g : PSc, g.toValue = v ∧ bsA = pscEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (A pA : BitVec 64) (ps : List (BitVec 64)) (l18' l20' spl' lo' : List UInt8),
          ps.length = 512 ∧ l18'.length = 8 ∧ l20'.length = 8 ∧ spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (l18'.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l20'.At (s.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 pA.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 101)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 64 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 36912)
          ⋆ Eq (g.pks.flatten.At s.regs.rbx.toBitVec) ⋆ Eq (g.aggregatePubkey.toList.At (s.regs.rbx.toBitVec + 24576))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 A.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 512).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 512).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 pA.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((lvHdrs 48 ps).At A) ⋆ lvElems ps g.pks ⋆ Eq (g.aggregatePubkey.toList.At pA)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Size reject (spec).** `bs.size ≠ 24624`: EthLib rejects, and the machine code returns the two words of
`ssz.ErrSize` (postcondition of `sc_reject_size_stmt`). -/
def sc_reject_size_spec_stmt : Prop :=
  ∀ (k : Nat) (hk : ScUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh ScUnmarshal k)
    (bs : Array UInt8) (hbs : bs.size ≠ 24624)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size),
    (∃ e, deserialize prysmScDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

/-- **Reject completeness (spec).** Every input that EthLib rejects has `size ≠ 24624`: the path condition of
the decoder's one reject site (`runtime.panicBounds` is not an error return; it is to be proved unreachable). -/
def sc_reject_complete_stmt : Prop :=
  ∀ bs : Array UInt8, (¬ ∃ v, deserialize prysmScDesc bs = .ok v) → bs.size ≠ 24624

end E2eList
