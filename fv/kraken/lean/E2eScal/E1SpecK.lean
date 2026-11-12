import E2eScal.E1Accept
import E2eScal.E1Reject
import E2eScal.E1Spec

/-!
# Spec alignment of the real Eth1Data decoder (hold-out)

Hand-written (the text of `BhSpecK.lean` with the Eth1Data statement).
- `e1_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmE1Desc`, the independent consensus-specs Desc)
  as `v`, there is `g : PE1` with `g.toValue = v` and `bsA = pe1Enc g`; with the input chunks of that `g`
  the machine code returns nil and the receiver holds `g` (the two roots at fresh `p1 p2` with
  len = cap = 32, DepositCount = `uintBytes 8`).
- `e1_e2e_reject_size_spec`: `bs.size ≠ 72` → EthLib rejects, and the machine code (with `rcx = bs.size`)
  returns the two words of `ssz.ErrSize`.
- `e1_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 72`, the path condition of the one
  reject site of the decoder (it has no other error return).
-/

open Machine Runtime TestTarget E2e E2eScal.E1Code E2eScal Codec EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.E1

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem e1_e2e_accept_spec_k (k : Nat) (hk : E1Unmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh E1Unmarshal k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmE1Desc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aN aP2 aL2 aC2 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (hast : ast.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8) (haN : aN.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PE1, bsA = pe1Enc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.depositRoot.toList.At s.regs.rbx.toBitVec)
      ⋆ Eq ((uintBytes 8 g.depositCount.toNat).toList.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq (g.blockHash.toList.At (s.regs.rbx.toBitVec + 40))
      ⋆ Eq (ast.At s.regs.rax.toBitVec)
      ⋆ Eq (aP1.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 24)) ⋆ Eq (aN.At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 48))
      ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 64 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ g : PE1, g.toValue = v ∧ bsA = pe1Enc g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ (p1 p2 : BitVec 64) (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq (spl'.At (s.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 70)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 64)
          ⋆ Eq (g.depositRoot.toList.At s.regs.rbx.toBitVec)
          ⋆ Eq ((uintBytes 8 g.depositCount.toNat).toList.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq (g.blockHash.toList.At (s.regs.rbx.toBitVec + 40))
          ⋆ Eq (ast.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((uintBytes 8 g.depositCount.toNat).toList.At (s.regs.rax.toBitVec + 32))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 48)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56))
          ⋆ Eq (g.depositRoot.toList.At p1) ⋆ Eq (g.blockHash.toList.At p2)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := pe1_accepted_is_enc hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h72 : s.regs.rcx = 72 := by
    apply UInt64.toNat_inj.mp; rw [hlen, pe1_enc_size]; rfl
  exact e1_e2e_accept_main k hk hf _ _ _ (by simp) (by simp [Spec.uintBytes_size]) (by simp) s ra guard
    fp s1 s2 spl l18 rslot lo ast aP1 aL1 aC1 aN aP2 aL2 aC2
    hfp h1 h2 hspl hl18 hrs hast haP1 haL1 haC1 haN haP2 haL2 haC2
    R S hlo Heap avail (Pm g rfl) hguard h72 hav hms hmm

/-- `len(buf) ≠ 72`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem e1_e2e_reject_size_spec (k : Nat) (hk : E1Unmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh E1Unmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 72)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmE1Desc bs = .error e) ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ :=
  ⟨pe1_spec_rejects bs hbs, e1_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site (path condition
`size ≠ 72`). -/
theorem e1_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmE1Desc bs = .ok v) :
    bs.size ≠ 72 := fun h72 => h ((pe1_spec_accepts_iff bs).mpr h72)

end E2eScal.E1
