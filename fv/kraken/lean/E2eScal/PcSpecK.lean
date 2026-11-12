import E2eScal.PcAccept
import E2eScal.PcReject
import E2eScal.PcSpec

/-!
# Spec alignment of the real PendingConsolidation decoder (hold-out, class D)

Hand-written: the text of `DdSpecK.lean` / `PwSpecK.lean`, with the statement
`pc_accept_stmt` (`H5Stmt.lean`) and the input chunks of `g`.
- `pc_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmPcDesc`) as `v`, there is `g : PPc` with `g.toValue = v`
  and `bsA = ppcEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
- `pc_e2e_reject_size_spec`: `bs.size ≠ 16` → EthLib rejects, and the machine code returns `ssz.ErrSize`.
- `pc_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 16` (the path condition of the size reject).
Not stated here: that the callee error paths (`fmt.errorf` wraps) are unreachable when `size = 16`.
-/

open Fk E2e E2eAd.Code E2eScal.H5Code E2eScal.BhCode E2eScal EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.H5

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the hand statement `pc_accept_stmt` for the input chunks of the `g` that EthLib decodes. -/
theorem pc_e2e_accept_spec_k (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PcUnmarshal k)
    (kV : Nat) (hkV : ViUnmarshal.IsInfixAt Host.prog kV) (hfV : LabelsFresh ViUnmarshal kV)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmPcDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 s4 sp1 rslot lo ast a8 a16 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h4 : s4.length = 8)
    (hsp1 : sp1.length = 8) (hrs : rslot.length = 8) (hlo : lo.length = 8)
    (hast : ast.length = 8) (ha8 : a8.length = 8) (ha16 : a16.length = 8)
    (R : DataMem → Prop)
    (Pm : ∀ g : PPc, bsA = ppcEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (sp1.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((uintBytes 8 g.sourceIndex.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.targetIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq (a8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (a16.At (s.regs.rax.toBitVec + 16)) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) :
    ∃ g : PPc, g.toValue = v ∧ bsA = ppcEnc g ∧
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 56)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((uintBytes 8 g.sourceIndex.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq ((uintBytes 8 g.targetIndex.toNat).toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (ast.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.sourceIndex.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((uintBytes 8 g.targetIndex.toNat).toList.At (s.regs.rax.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, hb⟩ := ppc_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 16 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, ppc_enc_size]; rfl
  exact pc_e2e_accept_main k hk hf kV hkV hfV _ _ (by simp [Fv.uintBytes_size]) (by simp [Fv.uintBytes_size])
    s ra guard fp s1 s2 s4 sp1 rslot lo ast a8 a16 hfp h1 h2 h4 hsp1 hrs hlo hast ha8 ha16
    R (Pm g hb) hguard hn

/-- `len(buf) ≠ 16`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem pc_e2e_reject_size_spec (k : Nat) (hk : PcUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh PcUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 16)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmPcDesc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨ppc_spec_rejects bs hbs, pc_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site (path condition
`size ≠ 16`). -/
theorem pc_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmPcDesc bs = .ok v) :
    bs.size ≠ 16 := fun h16 => h ((ppc_spec_accepts_iff bs).mpr h16)

end E2eScal.H5
