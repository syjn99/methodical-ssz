import E2eScal.PwAccept
import E2eScal.PwSpec

/-!
# Spec alignment of the real PendingPartialWithdrawal decoder, accept side (unit G5-C)

Written by the G5-C session: the accept part of `PcSpecK.lean` (H5) for PendingPartialWithdrawal, which
`PwSpecK.lean` (H4) left out because the accept theorem was not proved then (H4 attempt bound). The accept theorem
`pw_e2e_accept_main : pw_accept_stmt` was proved later (`PwAccept.lean`). This module adds only:
- `pw_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmPwDesc`) as `v`, there is `g : PPw` with `g.toValue = v`
  and `bsA = ppwEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
The statement text is `pw_accept_stmt` (`H4Stmt.lean`, unchanged) with the input chunks replaced by the encoding of
`g`. Not stated here: that the two callee error paths (`fmt.errorf` wraps) are unreachable when `size = 24`.
-/

open Fk E2e E2eAd.Code E2eScal.H4Code E2eScal.BhCode E2eScal EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.H4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the hand statement `pw_accept_stmt` for the input chunks of the `g` that EthLib decodes. -/
theorem pw_e2e_accept_spec_k : ∀ (k : Nat) (hk : PwUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PwUnmarshal k)
    (kV : Nat) (hkV : ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh ViUnmarshal kV)
    (kE : Nat) (hkE : E2e.Code.EpUnmarshal.IsInfixAt Host.prog kE) (hfE : LabelsFresh E2e.Code.EpUnmarshal kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmPwDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8) (ha24 : a24.length = 8)
    (R : DataMem → Prop)
    (Pm : ∀ g : PPw, bsA = ppwEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq ((uintBytes 8 g.withdrawableEpoch.toNat).toList.At (s.regs.rbx.toBitVec + 16))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (a24.At (s.regs.rax.toBitVec + 24)) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size),
    ∃ g : PPw, g.toValue = v ∧ bsA = ppwEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (sp1' lo' : List UInt8), sp1'.length = 8 ∧ lo'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 s.regs.rdi.toBitVec.toInt).At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (sp1'.At (s.regs.rsp.toBitVec - 72))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 60)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.withdrawableEpoch.toNat).toList.At (s.regs.rbx.toBitVec + 16))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.index.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((uintBytes 8 g.withdrawableEpoch.toNat).toList.At (s.regs.rax.toBitVec + 24)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  intro k hk hf kV hkV hfV kE hkE hfE bsA v hd s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 ha24 R Pm hguard hlen
  obtain ⟨g, rfl, hb⟩ := ppw_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 24 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, ppw_enc_size]; rfl
  exact pw_e2e_accept_main k hk hf kV hkV hfV kE hkE hfE _ _ _ (by simp [Fv.uintBytes_size])
    (by simp [Fv.uintBytes_size]) (by simp [Fv.uintBytes_size]) s ra guard
    fp s1 s2 s4 sp1 rslot lo ast a8 a16 a24 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16 ha24 R (Pm g hb) hguard hn

end E2eScal.H4
