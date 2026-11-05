import Fk.BvAccept
import Fv1.SpecBitVec
import Fv1.Transfer

/-!
# BitVec: size, length reject, EthLib links, and the padding-bit counterexample

`bv_padding_counterexample`: on the input byte 0x10 (a padding bit set) EthLib
rejects (`paddingBits`), and the machine code of BitVec.UnmarshalSSZ returns
nil with J = [0x10]. So the generated decoder accepts a non-canonical
encoding: its accepted set is larger than EthLib's (REPORT-1b, finding F1).
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
theorem bv_size_main (k : Nat) (hk : BitVecSizeSSZ.IsInfixAt Host.prog k) (s : MachineData) (ra : UInt64)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 1 ∧ st.data.regs.rsp = s.regs.rsp + 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem ⊢
  kat hk BitVecSizeSSZ 0
  kat hk BitVecSizeSSZ 1
  kat hk BitVecSizeSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bv_reject_size_main (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ 1) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk BitVecUnmarshalSSZ 0
  kat hk BitVecUnmarshalSSZ 1
  kat hk BitVecUnmarshalSSZ 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitVecUnmarshalSSZ 5
  kat hk BitVecUnmarshalSSZ 6
  kat hk BitVecUnmarshalSSZ 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (by bv_omega) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecUnmarshalSSZ 8
  kat hk BitVecUnmarshalSSZ 9
  kat hk BitVecUnmarshalSSZ 10
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 47
  kat hk BitVecUnmarshalSSZ 47
  kat hk BitVecUnmarshalSSZ 48
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 49
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 50
  kat hk BitVecUnmarshalSSZ 51
  rw [show 24 + (rsp.toBitVec - 8#64 - 24) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 52
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)

theorem bv_reject_spec (bs : Array UInt8) (h : bs.size ≠ 1) : ∃ e, deserialize bvDesc bs = .error e := by
  cases hd : deserialize bvDesc bs with
  | error e => exact ⟨e, rfl⟩
  | ok v =>
    obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := BitVecG.toValue) (enc := bvEncode) bvDesc_wellFormed
      bv_serialize bv_toValue_surjective hd
    exact absurd (bv_encode_size g) h

/-- EthLib acceptance gives a canonical byte; the machine accepts it into J. -/
theorem bv_unmarshal_accept_spec_k (bs : Array UInt8) (v : Value) (hd : deserialize bvDesc bs = .ok v) :
    ∃ g : BitVecG, g.toValue = v ∧ bs = #[g.b] := by
  obtain ⟨g, rfl, rfl⟩ := accepted_is_enc (toV := BitVecG.toValue) (enc := bvEncode) bvDesc_wellFormed
    bv_serialize bv_toValue_surjective hd
  exact ⟨g, rfl, rfl⟩

set_option maxHeartbeats 2000000 in
/-- **Accept path against EthLib, with the machine run** (1b-fix X7). If EthLib
accepts `bsA` as `v`, there is a canonical `g` (`g.b < 16`) with
`g.toValue = v`, `bsA = #[g.b]`, and BitVec.UnmarshalSSZ on that input byte
returns nil with J = (p, 1, 1) and `g.b` at p (`bv_accept_main`).
`bv_unmarshal_accept_spec_k` alone states only the byte equation. -/
theorem bv_unmarshal_accept_machine (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize bvDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : BitVecG, bsA = #[g.b] →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([g.b].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 40 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hav : 1 * 1 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
    ∃ g : BitVecG, g.toValue = v ∧ bsA = #[g.b] ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ p : BitVec 64, (Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 1).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ([g.b].At p)
          ⋆ Eq ([g.b].At s.regs.rbx.toBitVec) ⋆ Heap (avail - 1 * 1) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨g, hv, hb⟩ := bv_unmarshal_accept_spec_k bsA v hd
  refine ⟨g, hv, hb, ?_⟩
  have hrcx : s.regs.rcx = 1 := by
    apply UInt64.toNat_inj.mp; rw [hlen, hb]; rfl
  exact bv_accept_main k hk hf g.b s ra guard fp s1 s2 rslot cP cL cC hfp h1 h2 hrs hcP hcL hcC R S scratch spm hsc hspm
    Heap avail (P g hb) hguard hsp hrcx hav hms

/-- **Finding F1.** EthLib rejects [0x10]; the machine code accepts it. -/
theorem bv_padding_counterexample (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k) (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([0x10].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 40 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 1) (hav : 1 * 1 ≤ avail)
    (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
    deserialize bvDesc #[0x10] = .error .paddingBits ∧
    Eventually (step1 Host.exe) (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0)
      ⟨s, Host.addrOf k⟩ :=
  ⟨bv_spec_rejects_padding,
   eventually_trans _ _ _ _ (bv_accept_main k hk hf 0x10 s ra guard fp s1 s2 rslot cP cL cC hfp h1 h2 hrs hcP hcL hcC
      R S scratch spm hsc hspm Heap avail h_mem hguard hsp hlen hav hms) (fun _ h => Eventually.done _ ⟨h.1, h.2.1⟩)⟩

theorem bvm_s72 (x : BitVec 64) : x - 8#64 - 48 + 72 = x + 16 := by bv_omega
theorem bvm_s48 (x : BitVec 64) : 48 + (x - 8#64 - 48) = x - 8 := by bv_omega
theorem bvm_dst (x y : BitVec 64) : x + y * 1#64 = x + y := by rw [BitVec.mul_one]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **BitVec.MarshalSSZTo fast path**: len(J) = 1 and room in dst → appends J[0]
and returns (ptr, len + 1, cap, nil); `dst[:len]` unchanged. For a canonical
Go value (`BitVecG`) the byte is `bvEncode g` = EthLib `serialize`. -/
theorem bv_marshal_main (k : Nat) (hk : BitVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecMarshalSSZTo k) (b : UInt8) (p : BitVec 64)
    (s : MachineData) (ra guard : UInt64) (pre d0 fp slot : List UInt8)
    (hd0 : d0.length = 1) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (1 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ([b].At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 8 ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 1 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 1 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([b].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ([b].At p) ⋆ R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk BitVecMarshalSSZTo 0
  kat hk BitVecMarshalSSZTo 1
  kat hk BitVecMarshalSSZTo 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 3
  split
  · rename_i h; exfalso
    simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hk BitVecMarshalSSZTo 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk BitVecMarshalSSZTo 5
  kat hk BitVecMarshalSSZTo 6
  kat hk BitVecMarshalSSZTo 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (bvm_s72 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecMarshalSSZTo 8
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 9
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (1 : BitVec 64).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 10
  kat hk BitVecMarshalSSZTo 11
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BitVecMarshalSSZTo 12
  kat hk BitVecMarshalSSZTo 13
  kat hk BitVecMarshalSSZTo 14
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf BitVecMarshalSSZTo 28
  kat hk BitVecMarshalSSZTo 28
  kat hk BitVecMarshalSSZTo 29
  apply load_step _ _ _ _ [b] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk BitVecMarshalSSZTo 30
  rw [bvm_dst]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m3 H3
  simp only [Width.bytes, Width.bits, zx8, toBytes_ofInt_ofBytes 8 1 rfl [b] rfl] at H3
  kunfold
  kat hk BitVecMarshalSSZTo 31
  kat hk BitVecMarshalSSZTo 32
  kat hk BitVecMarshalSSZTo 33
  kat hk BitVecMarshalSSZTo 34
  intro _
  kat hk BitVecMarshalSSZTo 35
  intro _
  kat hk BitVecMarshalSSZTo 36
  kat hk BitVecMarshalSSZTo 37
  rw [bvm_s48]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 38
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_, ?_, trivial, ?_⟩
  all_goals first
    | trivial | rfl
    | (apply UInt64.toBitVec_inj.mp; simp; done)
    | (show (rcx.toBitVec + 1).toNat = rcx.toNat + 1; simp [BitVec.toNat_add]; omega)
    | exact sep_true (by ecancel)
