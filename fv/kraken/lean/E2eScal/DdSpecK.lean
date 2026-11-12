import E2eScal.DdAccept
import E2eScal.DdReject
import E2eScal.DdSpec

/-!
# Spec alignment of the real Deposit_Data decoder (hold-out, type A)

Hand-written: the text of `DmSpecK.lean` with the Deposit_Data statement
(receiver `state` word `ast` and the fourth field Signature).
- `dd_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmDdDesc`) as `v`, there is `g : PDd` with `g.toValue = v`
  and `bsA = pddEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
- `dd_e2e_reject_size_spec`: `bs.size ≠ 184` → EthLib rejects, and the machine code returns `ssz.ErrSize`.
- `dd_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 184`, the path condition of the one
  reject site of the decoder (it has no other error return).
-/

open Machine Runtime TestTarget E2e E2eScal.H4Code E2eScal Codec EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.H4

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem dd_e2e_accept_spec_k (k : Nat) (hk : DdUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh DdUnmarshal k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmDdDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8) (haN : aN.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PDd, bsA = pddEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.pubkey.toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.withdrawalCredentials.toList.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rbx.toBitVec + 80))
      ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aN.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 64)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 72))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 80))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 176 ≤ avail)
    (hms : MakesliceC Heap E2e.Data.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ g : PDd, g.toValue = v ∧ bsA = pddEnc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 p3 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 106)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 176)
          ⋆ Eq (g.pubkey.toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.withdrawalCredentials.toList.At (s.regs.rbx.toBitVec + 48))
          ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rbx.toBitVec + 80))
          ⋆ Eq (g.signature.toList.At (s.regs.rbx.toBitVec + 88))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 48).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((uintBytes 8 g.amount.toNat).toList.At (s.regs.rax.toBitVec + 56))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 72)) ⋆ Eq ((Int.toBytes 8 96).At (s.regs.rax.toBitVec + 80))
          ⋆ Eq (g.pubkey.toList.At p1) ⋆ Eq (g.withdrawalCredentials.toList.At p2) ⋆ Eq (g.signature.toList.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, hb⟩ := pdd_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have h88 : s.regs.rcx = 184 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, pdd_enc_size]; rfl
  exact dd_e2e_accept_main k hk hf _ _ _ _ (by simp) (by simp) (by simp [Spec.uintBytes_size]) (by simp) s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aP2 aL2 aC2 aN aP3 aL3 aC3
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haP2 haL2 haC2 haN haP3 haL3 haC3
    R S hlo Heap avail (Pm g hb) hguard h88 hav hms hmm

/-- `len(buf) ≠ 184`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem dd_e2e_reject_size_spec (k : Nat) (hk : DdUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh DdUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 184)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At E2e.Data.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmDdDesc bs = .error e) ∧
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
  ⟨pdd_spec_rejects bs hbs, dd_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site (path condition
`size ≠ 184`). -/
theorem dd_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmDdDesc bs = .ok v) :
    bs.size ≠ 184 := fun h88 => h ((pdd_spec_accepts_iff bs).mpr h88)

end E2eScal.H4
