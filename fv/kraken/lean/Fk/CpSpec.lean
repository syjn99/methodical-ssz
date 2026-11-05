import Fk.CpAccept
import Fk.FvSmall
import Fk.LuErr
import Fv1.SpecPrysm

/-!
# Prysm Checkpoint: size, length reject, accept path against EthLib (B3)

- `cp_size_main`: SizeSSZ returns 40.
- `cp_reject_size_main`: `len(buf) ≠ 40` → `ssz.ErrSize`.
- `cp_spec_accepts_iff`: EthLib accepts exactly the 40-byte inputs (every
  40-byte input is `cpEncode g` of one `g`), which is the one Go check.
- `cp_unmarshal_accept_spec_k`: on an input EthLib accepts as `v`, the
  machine code returns nil with the receiver holding the `g` with
  `g.toValue = v` (Epoch, and Root = (p, 32, 32) with the 32 bytes at p).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

theorem cp_size_main (k : Nat) (hk : PrysmCheckpointSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 40 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk PrysmCheckpointSizeSSZ 0
  kat hk PrysmCheckpointSizeSSZ 1
  kat hk PrysmCheckpointSizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem cp_reject_size_main (k : Nat) (hk : PrysmCheckpointUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 40) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk PrysmCheckpointUnmarshalSSZ 0
  kat hk PrysmCheckpointUnmarshalSSZ 1
  kat hk PrysmCheckpointUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk PrysmCheckpointUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 5
  kat hk PrysmCheckpointUnmarshalSSZ 6
  kat hk PrysmCheckpointUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 8
  kat hk PrysmCheckpointUnmarshalSSZ 9
  kat hk PrysmCheckpointUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf PrysmCheckpointUnmarshalSSZ 55
  kat hk PrysmCheckpointUnmarshalSSZ 55
  kat hk PrysmCheckpointUnmarshalSSZ 56
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 57
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 58
  kat hk PrysmCheckpointUnmarshalSSZ 59
  rw [show (32 : BitVec 64) + (rsp.toBitVec - 8#64 - 32) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk PrysmCheckpointUnmarshalSSZ 60
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · exact sep_true (by ecancel)

theorem cp_toValue_surjective' (v : Value) (h : Value.fits cpDesc v = true) : ∃ g : CheckpointG, g.toValue = v :=
  cp_toValue_surjective v h

/-- EthLib accepts exactly the 40-byte inputs. -/
theorem cp_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize cpDesc bs = .ok v) ↔ bs.size = 40 := by
  constructor
  · rintro ⟨v, hd⟩
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := CheckpointG) (toV := CheckpointG.toValue) (enc := cpEncode)
      cpDesc_wellFormed cp_serialize cp_toValue_surjective' hd
    exact cp_encode_size g
  · intro h
    have r8 := readUint_lt bs 0 8
    simp only [Nat.reducePow, Nat.reduceMul] at r8
    let g : CheckpointG := ⟨UInt64.ofNat (readUint bs 0 8), ⟨bs.extract 8 40, by simp; omega⟩⟩
    have e : bs = cpEncode g := by
      simp only [g, cpEncode, UInt64.toNat_ofNat_of_lt' r8, uintBytes_readUint_slice bs 0 8 (by omega)]
      rw [Array.extract_append_extract, show min 0 8 = 0 from rfl, show max 8 40 = bs.size by omega]; simp
    rw [e]
    exact ⟨_, deserialize_enc (G := CheckpointG) (toV := CheckpointG.toValue) (enc := cpEncode)
      cpDesc_wellFormed cp_serialize cp_toValue_fits g⟩

set_option maxHeartbeats 2000000 in
/-- **Accept path against EthLib.** If EthLib accepts `bsA` as `v`, there is
`g` with `g.toValue = v` and `bsA = cpEncode g`; with the input chunks of that
`g` the machine returns nil and the receiver holds `g`. -/
theorem cp_unmarshal_accept_spec_k (k : Nat) (hk : PrysmCheckpointUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh PrysmCheckpointUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize cpDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 l16 rslot c0 cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hrs : rslot.length = 8)
    (hc0 : c0.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : CheckpointG, bsA = cpEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec) ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (cP.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cL.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 48 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S) :
    ∃ g : CheckpointG, g.toValue = v ∧ bsA = cpEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ p : BitVec 64, (Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq (g.root.toList.At p)
          ⋆ Eq ((uintBytes 8 g.epoch.toNat).toList.At s.regs.rbx.toBitVec)
          ⋆ Eq (g.root.toList.At (s.regs.rbx.toBitVec + 8))
          ⋆ Heap (avail - 32) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := CheckpointG) (toV := CheckpointG.toValue) (enc := cpEncode)
    cpDesc_wellFormed cp_serialize cp_toValue_surjective' hd
  refine ⟨g, rfl, rfl, ?_⟩
  have h40 : s.regs.rcx = 40 := by
    apply UInt64.toNat_inj.mp; rw [hlen, cp_encode_size]; rfl
  exact cp_accept_main k hk hf _ _ (by simp [Fv.uintBytes_size]) (by simp) s ra guard fp s1 s2 l16 rslot c0 cP cL cC
    hfp h1 h2 hl16 hrs hc0 hcP hcL hcC R S scratch spm hsc hspm Heap avail (P g rfl) hguard hsp h40 hav hms hmm

/-- `len(buf) ≠ 40`: EthLib rejects; the machine returns `ssz.ErrSize`. -/
theorem cp_reject_size_spec (bs : Array UInt8) (h : bs.size ≠ 40) : ∃ e, deserialize cpDesc bs = .error e := by
  cases hd : deserialize cpDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v => exact absurd ((cp_spec_accepts_iff bs).mp ⟨v, hd⟩) h
