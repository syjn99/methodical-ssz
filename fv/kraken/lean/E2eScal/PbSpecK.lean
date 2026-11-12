import E2eScal.PbAccept
import E2eScal.PbReject
import E2eScal.PbSpec

/-!
# Spec alignment of the real PowBlock decoder (hold-out, full-proof type)

Hand-written: the shape of `DdSpecK.lean` with the PowBlock statement
(`H6.pb_accept_stmt`, `H6Stmt.lean`; the input chunks are those of the `g` that EthLib decodes).
- `pb_e2e_accept_spec_k`: if EthLib accepts `bsA` (`prysmPbDesc`) as `v`, there is `g : PPb` with `g.toValue = v`
  and `bsA = ppbEnc g`; with the input chunks of that `g` the machine code returns nil and the receiver holds `g`.
- `pb_e2e_reject_size_spec`: `bs.size ≠ 96` → EthLib rejects, and the machine code returns `ssz.ErrSize`.
- `pb_e2e_reject_complete`: every input that EthLib rejects has `size ≠ 96`, the path condition of the
  size reject site. The decoder has no other error return.
-/

open Machine Runtime TestTarget E2e E2eAd.Code E2eScal.H6Code E2eScal Codec EthLib.Serialization.Ssz
variable [Host]

namespace E2eScal.H6

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- Accept side: the hand statement `pb_accept_stmt` for the input chunks of the `g` that EthLib decodes. -/
theorem pb_e2e_accept_spec_k (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k) (hf : LabelsFresh PbUnmarshal k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize prysmPbDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8)
    (hspl : spl.length = 24) (hl18 : l18.length = 8) (hrs : rslot.length = 8)
    (haP1 : aP1.length = 8) (haL1 : aL1.length = 8) (haC1 : aC1.length = 8)
    (haP2 : aP2.length = 8) (haL2 : aL2.length = 8) (haC2 : aC2.length = 8)
    (haP3 : aP3.length = 8) (haL3 : aL3.length = 8) (haC3 : aC3.length = 8)
    (R : DataMem → Prop) (S : Nat) (hlo : lo.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (Pm : ∀ g : PPb, bsA = ppbEnc g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (l18.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (lo.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (g.blockHash.toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.parentHash.toList.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq ((uintBytes 32 g.totalDifficulty.val).toList.At (s.regs.rbx.toBitVec + 64))
      ⋆ Eq (aP1.At s.regs.rax.toBitVec) ⋆ Eq (aL1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (aC1.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (aP2.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (aL2.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (aC2.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (aP3.At (s.regs.rax.toBitVec + 48)) ⋆ Eq (aL3.At (s.regs.rax.toBitVec + 56))
      ⋆ Eq (aC3.At (s.regs.rax.toBitVec + 64))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bsA.size) (hav : 96 ≤ avail)
    (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S) :
    ∃ g : PPb, g.toValue = v ∧ bsA = ppbEnc g ∧
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
          ⋆ Eq ((Int.toBytes 8 (Host.addrOf (k + 104)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48))
          ⋆ Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 96)
          ⋆ Eq (g.blockHash.toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.parentHash.toList.At (s.regs.rbx.toBitVec + 32))
          ⋆ Eq ((uintBytes 32 g.totalDifficulty.val).toList.At (s.regs.rbx.toBitVec + 64))
          ⋆ Eq ((Int.toBytes 8 p1.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p2.toInt).At (s.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 40))
          ⋆ Eq ((Int.toBytes 8 p3.toInt).At (s.regs.rax.toBitVec + 48))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 56)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 64))
          ⋆ Eq (g.blockHash.toList.At p1) ⋆ Eq (g.parentHash.toList.At p2) ⋆ Eq ((uintBytes 32 g.totalDifficulty.val).toList.At p3)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, hb⟩ := ppb_accepted_is_enc hd
  refine ⟨g, rfl, hb, ?_⟩
  have hn : s.regs.rcx = 96 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb, ppb_enc_size]; rfl
  exact pb_e2e_accept_g4gen k hk hf _ _ _ (by simp) (by simp) (by simp [Spec.uintBytes_size]) s ra guard
    fp s1 s2 spl l18 rslot lo aP1 aL1 aC1 aP2 aL2 aC2 aP3 aL3 aC3
    hfp h1 h2 hspl hl18 hrs haP1 haL1 haC1 haP2 haL2 haC2 haP3 haL3 haC3
    R S hlo Heap avail (Pm g hb) hguard hn hav hms hmm

/-- `len(buf) ≠ 96`: EthLib rejects, and the machine code returns the two words of `ssz.ErrSize`. -/
theorem pb_e2e_reject_size_spec (k : Nat) (hk : PbUnmarshal.IsInfixAt Host.prog k)
    (hf : LabelsFresh PbUnmarshal k) (bs : Array UInt8) (hbs : bs.size ≠ 96)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.CheckpointAndEpoch.e2eErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat = bs.size) :
    (∃ e, deserialize prysmPbDesc bs = .error e) ∧
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
  ⟨ppb_spec_rejects bs hbs, pb_e2e_reject_size_main k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard
    (fun h => hbs (by rw [← hlen, h]; rfl))⟩

/-- **`reject_complete`**: an input that EthLib rejects reaches the `ssz.ErrSize` site (path condition
`size ≠ 96`). -/
theorem pb_e2e_reject_complete (bs : Array UInt8) (h : ¬ ∃ v, deserialize prysmPbDesc bs = .ok v) :
    bs.size ≠ 96 := fun hz => h ((ppb_spec_accepts_iff bs).mpr hz)

end E2eScal.H6
