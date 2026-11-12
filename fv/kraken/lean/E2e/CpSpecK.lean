import E2e.CpAccept
import E2e.CpReject
import E2e.Spec

/-!
# Spec alignment of the real Checkpoint decoder

- `cp_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmCpDesc`) as `v`, there is
  `g : PCp` with `g.toValue = v` and `bsA = pcpEnc g`; with the input chunks of
  that `g` the machine code returns nil and the receiver holds `g` (Epoch field =
  `uintBytes 8 g.epoch`, `Root` = `(p, 32, 32)` with `g.root` at `p`).
- `cp_e2e_reject_size_spec`: `bs.size ≠ 40` → EthLib rejects, and the machine code
  (with `rcx = bs.size`) returns the two words of `ssz.ErrSize`.
- `cp_e2e_reject_complete` (obligation `reject_complete`): every input that EthLib
  rejects has `size ≠ 40`, which is the path condition of the one reject site of
  `UnmarshalSSZ` (`return ssz.ErrSize`, `cp_e2e_reject_size_main`). Join: the
  machine accepts only `size = 40` inputs (every other size takes the ErrSize
  return); EthLib accepts exactly those (`pcp_spec_accepts_iff`). So the accepted
  sets agree. The second Go-source reject site (`fmt.Errorf("Epoch: %w")`) is not
  reachable (`cp_e2e_epoch_err_unreachable`, `unreachable_mc` column): it is not
  needed for the join and is not counted as reject coverage.
-/

open Machine Runtime TestTarget E2e.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2e

set_option maxHeartbeats 4000000 in
theorem cp_e2e_accept_spec_k (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh CpUnmarshal k)
    (kE : Nat) (hkE : EpUnmarshal.IsInfixAt Host.prog kE) (hfE : LabelsFresh EpUnmarshal kE)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmCpDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl20 : l20.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hm0 : m0.length = 8) (hm1 : m1.length = 8)
    (hm2 : m2.length = 8) (hrs : rslot.length = 8) (hcst : cst.length = 8) (hc0 : c0.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (R : DataMem → Prop) (S : Nat) (hS8 : 8 ≤ S) (hS : S < 2 ^ 60) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PCp, bsA = pcpEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (m2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (m1.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (m0.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ g : PCp, g.toValue = v ∧ bsA = pcpEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p : BitVec 64) (scr mm : List UInt8), scr.length = S ∧ mm.length = 24 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 0).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (mm.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 96))
          ⋆ Eq (scr.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (g.root.toList.At p)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := pcp_accepted_is_enc hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h40 : s.regs.rcx = 40 := by
    apply UInt64.toNat_inj.mp; rw [hlen, pcp_enc_size]; rfl
  exact cp_e2e_accept_main k hk hf kE hkE hfE _ _ (by simp [Spec.uintBytes_size]) (by simp) s ra guard
    fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0 hcP
    hcL hcC hctl R S hS8 hS scratch hsc Heap avail (Pm g rfl) hguard h40 hav hms hmm

/-- `len(buf) ≠ 40`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem cp_e2e_reject_size_spec (k : Nat) (hk : CpUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh CpUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 40)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmCpDesc bs = .error e) ∧
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
  ⟨pcp_spec_rejects bs hbs, cp_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize`
site (path condition `size ≠ 40`). -/
theorem cp_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmCpDesc bs = .ok v) :
    bs.size ≠ 40 := fun h40 => h ((pcp_spec_accepts_iff bs).mpr h40)

end E2e
