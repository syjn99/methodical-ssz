import Prysm.VoluntaryExit.GeneratedDecodeAccept
import Prysm.VoluntaryExit.Spec

/-!
# Spec alignment of the real VoluntaryExit decoder

Built on the GENERATED theorems of `Prysm/VoluntaryExit/GeneratedDecodeAccept.lean` (`decoder --whole-accept`; raw output, not edited):
- `Decode.accept_spec`: if EthLib accepts `bsA` (`desc`) as `v`, there is `g : SszValue` with `g.toValue = v`
  and `bsA = SszValue.encode g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
  The statement is the generated accept statement (kind instance) with the input chunks replaced by the
  encoding of `g` (text written by a scratch script from the generated statement; then checked by Lean
  against `Prysm.VoluntaryExit.Decode.generated_accept`).
- `Decode.reject_size_spec`: `bs.size ≠ 16` → EthLib rejects, and the machine code returns `ssz.ErrSize`
  (generated `Decode.generated_reject`).
- `Decode.reject_complete`: every input that EthLib rejects has `size ≠ 16` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = 16`.
-/

open Machine Runtime Codec Prysm.VoluntaryExit.Code EthLib.Serialization.Ssz
variable [Host]

namespace Prysm.VoluntaryExit

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the generated accept statement for the input chunks of the `g` that EthLib decodes. -/
theorem Decode.accept_spec : ∀ (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (kV : Nat) (hkV : Prysm.ValidatorIndex.Code.unmarshalSSZ.IsInfixAt Host.prog kV) (hfV : LabelsFresh Prysm.ValidatorIndex.Code.unmarshalSSZ kV)
    (bsA : Array UInt8) (v : Value) (hd : deserialize desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 : List UInt8)
    (hfp : fp.length = 8) (hs1 : s1.length = 8) (hs2 : s2.length = 8) (hs4 : s4.length = 8) (hsp1 : sp1.length = 8) (hrslot : rslot.length = 8) (hlo : lo.length = 8) (hast : ast.length = 8) (haN0 : aN0.length = 8) (haN1 : aN1.length = 8)
    (R : DataMem → Prop)
    (Pm : ∀ g : SszValue, bsA = SszValue.encode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8))
      ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aN0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aN1.At (s.regs.rax.toBitVec + 16))
      ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size),
    ∃ g : SszValue, g.toValue = v ∧ bsA = SszValue.encode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (x0 x1 : List UInt8), x0.length = 8 ∧ x1.length = 8 ∧ 
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (x0.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (x1.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.validatorIndex.toNat).toList.At (s.regs.rax.toBitVec + 16))
          ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kE hkE hfE kV hkV hfV bsA v hd s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R Pm hguard hlen
  obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 16 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, SszValue.enc_size]; rfl
  exact Prysm.VoluntaryExit.Decode.generated_accept k hk hf kE hkE hfE kV hkV hfV _ _ (by simp [Spec.uintBytes_size]) (by simp [Spec.uintBytes_size]) s ra guard fp s1 s2 s4 sp1 rslot lo ast aN0 aN1 hfp hs1 hs2 hs4 hsp1 hrslot hlo hast haN0 haN1 R (Pm g hb) hguard hn

/-- `len(buf) ≠ 16`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem Decode.reject_size_spec (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh unmarshalSSZ k) (bs : Array UInt8) (hbs : bs.size ≠ 16)
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
  ⟨SszValue.spec_rejects bs hbs, Prysm.VoluntaryExit.Decode.generated_reject k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects has `size ≠ 16`: the path condition of the size reject.
(The callee error returns are not covered.) -/
theorem Decode.reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize desc bs = .ok v) :
    bs.size ≠ 16 := fun h16 => h ((SszValue.spec_accepts_iff bs).mpr h16)

end Prysm.VoluntaryExit
