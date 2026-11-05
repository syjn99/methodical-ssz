import Fk.BlAccept
import Fk.LuReject

/-!
# BitL: decoder rejects without calls, SizeSSZ, and the EthLib link (B3)

- `bl_reject_short_main`: `len(buf) < 4` → `ssz.ErrSize`.
- `bl_reject_offset_main`: offset (bytes 0..3) ≠ 4 → `ssz.ErrInvalidVariableOffset`.
- `bl_size_main`: SizeSSZ returns 4 + len(c.B).
- `bl_accepted_valid`: every input EthLib accepts is `offset 4 ‖ tl` with
  `tl` non-empty and `blValid tl`, so the contract gives rax = 0 and
  `bl_accept_main` applies (`bl_unmarshal_accept_spec_k`).
- `bl_spec_rejects`: `len < 4`, offset ≠ 4, or `¬ blValid buf[4:]` make EthLib
  reject. The last one is the check behind `ValidateBitlistC`; its Go error
  path (`fmt.Errorf("B: %w")`) is not proved here.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bl_reject_short_main (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 4) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk BitLUnmarshalSSZ 0
  kat hk BitLUnmarshalSSZ 1
  kat hk BitLUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLUnmarshalSSZ 5
  kat hk BitLUnmarshalSSZ 6
  kat hk BitLUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLUnmarshalSSZ 8
  kat hk BitLUnmarshalSSZ 9
  kat hk BitLUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf BitLUnmarshalSSZ 119
  kat hk BitLUnmarshalSSZ 119
  kat hk BitLUnmarshalSSZ 120
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 121
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 122
  kat hk BitLUnmarshalSSZ 123
  rw [show (112 : BitVec 64) + (rsp.toBitVec - 8#64 - 112) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 124
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

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bl_reject_offset_main (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (o4 : List UInt8) (ho4 : o4.length = 4) (hoff : Int.ofBytes o4 ≠ 4)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (o4.At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrInvalidVariableOffset" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : 4 ≤ s.regs.rcx.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk BitLUnmarshalSSZ 0
  kat hk BitLUnmarshalSSZ 1
  kat hk BitLUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitLUnmarshalSSZ 5
  kat hk BitLUnmarshalSSZ 6
  kat hk BitLUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitLUnmarshalSSZ 8
  kat hk BitLUnmarshalSSZ 9
  kat hk BitLUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk BitLUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ o4 _ _ (by bv_omega) (by ecancel) (by exact ho4)
  kunfold
  kat hk BitLUnmarshalSSZ 12
  kat hk BitLUnmarshalSSZ 13
  kat hk BitLUnmarshalSSZ 14
  kat hk BitLUnmarshalSSZ 15
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hoff (lu_off4 o4 ho4 h)
  simp only [Effects.All]
  klabel hk hf BitLUnmarshalSSZ 113
  kat hk BitLUnmarshalSSZ 113
  kat hk BitLUnmarshalSSZ 114
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 115
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 116
  kat hk BitLUnmarshalSSZ 117
  rw [show (112 : BitVec 64) + (rsp.toBitVec - 8#64 - 112) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLUnmarshalSSZ 118
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

theorem bl_size_main (k : Nat) (hk : BitLSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (n : Nat) (hn : n < 2 ^ 60) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (s.regs.rax.toBitVec + 8)) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax.toNat = 4 + n
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk BitLSizeSSZ 0
  kat hk BitLSizeSSZ 1
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitLSizeSSZ 2
  kat hk BitLSizeSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, trivial⟩
  · show (4 + BitVec.ofNat 64 n).toNat = _
    simp [BitVec.toNat_add]; omega
  · apply UInt64.toBitVec_inj.mp; simp

theorem packBitsDelimited_ne (b : Array Bool) : 1 ≤ (packBitsDelimited b).size := by
  simp [packBitsDelimited, packBits]

/-- Every input EthLib accepts is `offset 4 ‖ tl`, `tl` non-empty, `blValid tl`. -/
theorem bl_accepted_valid (bs : Array UInt8) (v : Value) (hd : deserialize blDesc bs = .ok v) :
    ∃ g : BitLG, blToValue g = v ∧ bs = blEncode g ∧ 1 ≤ (packBitsDelimited g.1).size
      ∧ blValid (packBitsDelimited g.1).toList := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (G := BitLG) (toV := blToValue) (enc := blEncode)
    blDesc_wellFormed bl_serialize bl_toValue_surjective hd
  refine ⟨g, rfl, rfl, packBitsDelimited_ne _, g.1, ?_⟩
  simp only [Array.toArray_toList]
  exact unpackDelimited_packBitsDelimited (some 2048) g.1 (fun cap h => by cases h; exact g.2)

theorem bl_tail (g : BitLG) : (blEncode g).extract 4 (blEncode g).size = packBitsDelimited g.1 := by
  have h4 : (uintBytes 4 4).size = 4 := by simp [Fv.uintBytes_size]
  have : ((uintBytes 4 4) ++ packBitsDelimited g.1).extract (uintBytes 4 4).size
      ((uintBytes 4 4) ++ packBitsDelimited g.1).size = packBitsDelimited g.1 := by
    apply Array.ext <;> simp
  rw [h4] at this; exact this

/-- Each failing Go check makes EthLib reject (the last one is behind the contract). -/
theorem bl_spec_rejects (bs : Array UInt8)
    (h : bs.size < 4 ∨ readUint bs 0 4 ≠ 4 ∨ ¬ blValid (bs.extract 4 bs.size).toList) :
    ∃ e, deserialize blDesc bs = .error e := by
  cases hd : deserialize blDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    exfalso
    obtain ⟨g, -, rfl, -, hv⟩ := bl_accepted_valid bs v hd
    have hs := bl_encode_size g
    rcases h with h | h | h
    · omega
    · exact h (by simp only [blEncode]; exact readUint_uintBytes_prefix _ 4 4 (by decide))
    · rw [bl_tail] at h; exact h hv

set_option maxHeartbeats 2000000 in
/-- **Accept path against EthLib** (behind `ValidateBitlistC`). If EthLib
accepts `bsA` as `v`, there is `g` (at most 2048 bits) with `blToValue g = v`,
`bsA = blEncode g`, and the machine returns nil with `c.B` holding the bytes
`packBitsDelimited g.1` (the Go `Bitlist` keeps the delimiter). -/
theorem bl_unmarshal_accept_spec_k (k : Nat) (hk : BitLUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitLUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize blDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s8 s16 s24 l32 l40 l48 l56 l64 l72 l80 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h8 : s8.length = 8) (h16 : s16.length = 8) (h24 : s24.length = 8)
    (hl32 : l32.length = 8) (hl40 : l40.length = 8) (hl48 : l48.length = 8) (hl56 : l56.length = 8)
    (hl64 : l64.length = 8) (hl72 : l72.length = 8) (hl80 : l80.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : BitLG, bsA = blEncode g →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s16.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s24.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l40.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l48.At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (l56.At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq (l64.At (s.regs.rsp.toBitVec - 64)) ⋆ Eq (l72.At (s.regs.rsp.toBitVec - 72))
      ⋆ Eq (l80.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 128 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((packBitsDelimited g.1).toList.At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 128 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat)
    (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hvb : ValidateBitlistC S) (hgs : GrowsliceC Heap (label "type__" + 48736).toBitVec 1 S) (hmm : MemmoveC S) :
    ∃ g : BitLG, blToValue g = v ∧ bsA = blEncode g ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧
        ∃ (p : BitVec 64) (c : Nat) (rest : List UInt8), (packBitsDelimited g.1).toList.length + rest.length = c ∧
          (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (packBitsDelimited g.1).toList.length).toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 c).toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((packBitsDelimited g.1).toList.At p)
          ⋆ Eq (rest.At (p + BitVec.ofNat 64 (packBitsDelimited g.1).toList.length))
          ⋆ Eq ((packBitsDelimited g.1).toList.At (s.regs.rbx.toBitVec + 4)) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, rfl, rfl, hne, hv⟩ := bl_accepted_valid bsA v hd
  refine ⟨g, rfl, rfl, ?_⟩
  exact bl_accept_main k hk hf _ (by simpa using hne) hv s ra guard fp s8 s16 s24 l32 l40 l48 l56 l64 l72 l80 rslot
    cP cL cC hfp h8 h16 h24 hl32 hl40 hl48 hl56 hl64 hl72 hl80 hrs hcP hcL hcC R S scratch hsc Heap avail
    (P g rfl) hguard hsp (by rw [hlen, bl_encode_size]; simp [packBitsDelimited, packBits]) hcap hcap63 hvb hgs hmm
