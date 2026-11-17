import Prysm.SyncCommitteeMessage.GeneratedDecodeAccept
import Prysm.SyncCommitteeMessage.Spec
import Prysm.SyncCommitteeMessage.Code
import Prysm.Slot.Code
import Prysm.ValidatorIndex.Code

/-!
# Spec alignment of the `v1alpha1.SyncCommitteeMessage` decoder

Built on the GENERATED theorems of `Prysm/SyncCommitteeMessage/GeneratedDecodeAccept.lean` (the `decoder --whole-accept` row of the type in `gen/generator/types.tsv`, run by `gen/generator/gen.sh`):
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`) as `v`, there is `g : SszValue` with `g.toValue = v`
  and `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by `gen/flat-types/flat_types_decode_spec.py` from the generated statement; then checked
  by Lean against `Prysm.SyncCommitteeMessage.Decode.generated_accept`).
- `Decode.reject_size_spec`: `bs.size ≠ 144` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `Decode.generated_reject`).
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ 144` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = 144`.
-/

open Machine Runtime Codec Prysm.SyncCommitteeMessage.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.SyncCommitteeMessage

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem Decode.accept_spec : ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kS : Nat) (hkS : Prysm.Slot.Code.unmarshalSSZ.IsInfixAt Host.prog kS) (hfS : LabelsFresh Prysm.Slot.Code.unmarshalSSZ kS)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp0 sp1 sp2 l28 l30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp0 : sp0.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8) (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hl38 : l38.length = 8) (hrslot : rslot.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN2 : aN2.length = 8) (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hS : S < 2 ^ 60) (hlo : lo.length = S + 8)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp0.At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (sp2.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l38.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 112))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq (g.blockRoot.toArray.toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rbx.toBitVec + 40))
      ⋆ Eq (g.signature.toArray.toList.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aN2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ R)
    (hguard : guard.toNat + 112 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 128 ≤ avail)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (S + 8)) (hmm : MemmoveContract (S + 8)),
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (x0 x1 : List UInt8), x0.length = 24 ∧ x1.length = S + 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 104))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 64))
          ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.rsp.toBitVec - 56))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 141)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 112))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 128)
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq (g.blockRoot.toArray.toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (g.signature.toArray.toList.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((uintBytes 8 g.slot.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (g.blockRoot.toArray.toList.At p1)
          ⋆ Eq (g.signature.toArray.toList.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kS hkS hfS kV hkV hfV bsA v hd s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 l30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hl30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail Pm hguard hlen hav hms hmm
  obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 144 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, SszValue.encode_size]; rfl
  exact Prysm.SyncCommitteeMessage.Decode.generated_accept k hk hf kS hkS hfS kV hkV hfV _ _ _ _ (by simp [Spec.uintBytes_size]) (by simp) (by simp [Spec.uintBytes_size]) (by simp) s ra guard fp s1 s2 s4 sp0 sp1 sp2 l28 l30 l38 rslot lo ast aN0 aP1 aL1 aC1 aN2 aP3 aL3 aC3 hfp hs1 hs2 hs4 hsp0 hsp1 hsp2 hl28 hl30 hl38 hrslot hast haN0 haP1 haL1 haC1 haN2 haP3 haL3 haC3 R S hS hlo Heap avail (Pm g hb) hguard hn hav hms hmm

/-- `len(buf) ≠ 144`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ 144)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨SszValue.spec_rejects bs hbs, Prysm.SyncCommitteeMessage.Decode.generated_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ 144`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ 144 := fun h144 => h ((SszValue.spec_accepts_iff bs).mpr h144)

end Prysm.SyncCommitteeMessage
