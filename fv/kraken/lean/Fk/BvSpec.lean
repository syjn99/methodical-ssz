import Fk.BvAccept
import Fk.LuRejectCall
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
  klabel hk hf BitVecUnmarshalSSZ 83
  kat hk BitVecUnmarshalSSZ 83
  kat hk BitVecUnmarshalSSZ 84
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 85
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 86
  kat hk BitVecUnmarshalSSZ 87
  rw [show 72 + (rsp.toBitVec - 8#64 - 72) = rsp.toBitVec - 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 88
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
/-- **Accept path against EthLib, with the machine run** (1b-fix X7, regenerated
code). If EthLib accepts `bsA` as `v`, there is a canonical `g` (`g.b < 16`)
with `g.toValue = v`, `bsA = #[g.b]`, and BitVec.UnmarshalSSZ on that input
byte returns nil with J = (p, 1, 1) and `g.b` at p (`bv_accept_main`). -/
theorem bv_unmarshal_accept_machine (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (bsA : Array UInt8) (v : Value) (hd : deserialize bvDesc bsA = .ok v)
    (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 f40 f32 rslot cP cL cC : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h40 : f40.length = 8) (h32 : f32.length = 8)
    (hrs : rslot.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (h8S : 8 ≤ S)
    (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (P : ∀ g : BitVecG, bsA = #[g.b] →
      s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (f40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (f32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([g.b].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hsp : 96 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = bsA.size) (hav : 1 * 1 ≤ avail)
    (hvbv : VbvAccC) (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
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
  refine eventually_trans _ _ _ _ (bv_accept_main k hk hf g.b g.hb s ra guard fp s1 s2 f40 f32 rslot cP cL cC hfp h1 h2
    h40 h32 hrs hcP hcL hcC R S scratch spm hsc h8S hspm Heap avail (P g hb) hguard hsp hrcx hav hvbv hms) ?_
  rintro st ⟨e1, e2, e3, e4, e5, e6, p, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hm⟩
  exact Eventually.done _ ⟨e1, e2, e3, e4, e5, e6, p, sep_true (by ecancel)⟩

theorem bvm_dst (x y : BitVec 64) : x + y * 1#64 = x + y := by rw [BitVec.mul_one]
theorem bvm_call (x : BitVec 64) : x - 8#64 - 80 - 8#64 = x - 96 := by bv_omega
theorem bvm_o (x : BitVec 64) (c : Nat) : x - 8#64 - 80 + BitVec.ofNat 64 c = x - 88 + BitVec.ofNat 64 c := by bv_omega
theorem bvm_b (x : BitVec 64) : ({ toBitVec := x - 96 } + 8 : UInt64).toBitVec = x - 88 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bvm_a (x c : BitVec 64) : x - 8#64 - 80 + c = x - 88 + c := by bv_omega
theorem bvm_96 (x : BitVec 64) : x - 88 + 96 = x + 8 := by bv_omega
theorem bvm_104 (x : BitVec 64) : x - 88 + 104 = x + 16 := by bv_omega
theorem bvm_112 (x : BitVec 64) : x - 88 + 112 = x + 24 := by bv_omega
theorem bvm_120 (x : BitVec 64) : x - 88 + 120 = x + 32 := by bv_omega
theorem bvm_80 (x : BitVec 64) : (80 : BitVec 64) + (x - 88) = x - 8 := by bv_omega
theorem bvm_fp (x : BitVec 64) : x - 96 - 8 = x - 104 := by bv_omega
theorem bvm_sp (x : BitVec 64) : x - 96 + 8 = x - 88 := by bv_omega
theorem bvm_scr (x : BitVec 64) (S : Nat) (h : 8 ≤ S) :
    x - 96 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - 8) = x - 104 := by
  have : BitVec.ofNat 64 (S - 8) = BitVec.ofNat 64 S - 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [this]; bv_omega
theorem bvm_nat (x : UInt64) (h : 96 ≤ x.toNat) : (x.toBitVec - 96).toNat = x.toNat - 96 := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
theorem bvm_one : BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (1 : BitVec 64).toInt)) = 1 := by decide

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **BitVec.MarshalSSZTo fast path** (regenerated code): J = (p, 1, c) with a
canonical byte `b` (`b < 16`) at p and room in dst. The function calls
`ssz.ValidateBitvector(J, 4)` (nil, `VbvAccC`), appends J[0] and returns
(ptr, len + 1, cap, nil); `dst[:len]` unchanged. Every stack chunk comes back
(existentially). For a canonical Go value the byte is `bvEncode g` = EthLib
`serialize`. -/
theorem bv_marshal_main (k : Nat) (hk : BitVecMarshalSSZTo.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecMarshalSSZTo k) (b : UInt8) (hb : b.toNat < 16) (p : BitVec 64) (c : UInt64)
    (s : MachineData) (ra guard : UInt64) (pre d0 fp sl1 sl2 sl3 sl4 rslot vsp scratch : List UInt8)
    (hd0 : d0.length = 1) (hfp : fp.length = 8) (h1 : sl1.length = 8) (h2 : sl2.length = 8) (h3 : sl3.length = 8)
    (h4 : sl4.length = 8) (hrs : rslot.length = 8) (hvs : vsp.length = 8) (S : Nat) (hsc : scratch.length = S)
    (h8S : 8 ≤ S) (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sl1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (sl2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (sl3.At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq (sl4.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq (vsp.At (s.regs.rsp.toBitVec - 88))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (1 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 c.toBitVec.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([b].At p)
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (d0.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec)) ⋆ R)
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 104 + S ≤ s.regs.rsp.toNat)
    (hcap : s.regs.rcx.toNat + 1 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hvbv : VbvAccC) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + 1 ∧ st.data.regs.rcx = s.regs.rdi
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
        ∃ fp' sl1' sl2' sl3' sl4' rs' vsp' sc' : List UInt8, fp'.length = 8 ∧ sl1'.length = 8 ∧ sl2'.length = 8
          ∧ sl3'.length = 8 ∧ sl4'.length = 8 ∧ rs'.length = 8 ∧ vsp'.length = 8 ∧ sc'.length = S ∧
        (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ([b].At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
          ⋆ Eq ([b].At p)
          ⋆ Eq ((Int.toBytes 8 p.toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (1 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 c.toBitVec.toInt).At (s.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sl1'.At (s.regs.rsp.toBitVec + 8))
          ⋆ Eq (sl2'.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (sl3'.At (s.regs.rsp.toBitVec + 24))
          ⋆ Eq (sl4'.At (s.regs.rsp.toBitVec + 32))
          ⋆ Eq (rs'.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (sc'.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq (vsp'.At (s.regs.rsp.toBitVec - 88))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  have hS64 : S < 2 ^ 64 := by omega
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
  rw [bvm_a, bvm_96]
  apply store_step _ _ _ _ _ sl1 _ _ (by ecancel) (by exact h1)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecMarshalSSZTo 8
  rw [bvm_a, bvm_120]
  apply store_step _ _ _ _ _ sl4 _ _ (by ecancel) (by exact h4)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitVecMarshalSSZTo 9
  rw [bvm_a, bvm_112]
  apply store_step _ _ _ _ _ sl3 _ _ (by ecancel) (by exact h3)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitVecMarshalSSZTo 10
  rw [bvm_a, bvm_104]
  apply store_step _ _ _ _ _ sl2 _ _ (by ecancel) (by exact h2)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk BitVecMarshalSSZTo 11
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 12
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (1 : BitVec 64).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 13
  apply load_step_at _ _ (rax.toBitVec + 16) _ _ (Int.toBytes 8 c.toBitVec.toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 14
  kat hk BitVecMarshalSSZTo 15
  kat hk BitVecMarshalSSZTo 16
  rw [bvm_call]
  apply store_step _ _ _ _ _ rslot _ _ (by ecancel) (by exact hrs)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  rw [← List.take_append_drop (S - 8) scratch, Mem.At_append_sep _ _ _ (by simp [hsc]; omega)] at H6
  simp only [List.length_take, hsc, show min (S - 8) S = S - 8 by omega, bvm_scr _ S h8S] at H6
  try simp only [bvm_one, Fk.ofInt_ofBytes_toBytes64]
  refine eventually_trans _ _ _ _ (hvbv _ (Host.addrOf (k + 16 + 1)) guard (scratch.drop (S - 8)) vsp [] b _
    (by simp [hsc]; omega) hvs ?g1 ?g2 ?g3 ?g4 ?g5 ?g6
    (by dsimp only; rw [bvm_fp, bvm_sp, List.nil_append]; ecancel)) ?_
  case g1 => dsimp only; show guard.toNat < (rsp.toBitVec - 96).toNat; rw [bvm_nat _ (by omega)]; omega
  case g2 => dsimp only; show 8 ≤ (rsp.toBitVec - 96).toNat; rw [bvm_nat _ (by omega)]; omega
  case g3 => dsimp only; rfl
  case g4 => dsimp only; rfl
  case g5 => dsimp only; simp; decide
  case g6 => dsimp only; exact bva_shr4 b hb
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, fp2, sp2, hfp2, hsp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only [List.nil_append] at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hrax2 hrbx2 hrsp2 hrbp2 hr142
  rw [bvm_fp, bvm_sp] at Hm2
  kat hk BitVecMarshalSSZTo 17
  kat hk BitVecMarshalSSZTo 18
  intro _
  kat hk BitVecMarshalSSZTo 19
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf BitVecMarshalSSZTo 51
  kat hk BitVecMarshalSSZTo 51
  kat hk BitVecMarshalSSZTo 52
  rw [bvm_b, bvm_96]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 53
  apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 54
  apply load_step_at _ _ (rax.toBitVec + 8) _ _ (Int.toBytes 8 (1 : BitVec 64).toInt) _ _ (by kaddr) (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 55
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk BitVecMarshalSSZTo 56
  rw [bvm_b, bvm_112]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 57
  kat hk BitVecMarshalSSZTo 58
  rw [bvm_b, bvm_120]
  apply load_step _ _ _ _ (Int.toBytes 8 rdi.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 59
  kat hk BitVecMarshalSSZTo 60
  split
  case isTrue h =>
    exfalso; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  kat hk BitVecMarshalSSZTo 61
  rw [bvm_b, bvm_104]
  apply load_step _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 62
  klabel hk hf BitVecMarshalSSZTo 78
  kat hk BitVecMarshalSSZTo 78
  kat hk BitVecMarshalSSZTo 79
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]
  apply load_step _ _ _ _ [b] _ _ (by ecancel) (by rfl)
  kunfold
  kat hk BitVecMarshalSSZTo 80
  rw [bvm_dst]
  apply store_step _ _ _ _ _ d0 _ _ (by ecancel) (by exact hd0)
  intro m7 H7
  simp only [Width.bytes, Width.bits, zx8, toBytes_ofInt_ofBytes 8 1 rfl [b] rfl] at H7
  kunfold
  kat hk BitVecMarshalSSZTo 81
  kat hk BitVecMarshalSSZTo 82
  kat hk BitVecMarshalSSZTo 83
  kat hk BitVecMarshalSSZTo 84
  kat hk BitVecMarshalSSZTo 85
  kat hk BitVecMarshalSSZTo 86
  rw [bvm_b, bvm_80]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecMarshalSSZTo 87
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec from vbv_ret _]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  have hscr : (scratch.take (S - 8) ++ fp2).length = S := by simp [hsc, hfp2]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rax.toBitVec.toInt,
    Int.toBytes 8 rbx.toBitVec.toInt, Int.toBytes 8 rcx.toBitVec.toInt, Int.toBytes 8 rdi.toBitVec.toInt,
    Int.toBytes 8 (Host.addrOf (k + 16 + 1)).toBitVec.toInt, sp2, scratch.take (S - 8) ++ fp2,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _, Int.toBytes_length 8 _,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, hsp2, hscr, ?mem⟩
  case mem =>
    dsimp only
    rw [Mem.At_append_sep _ _ _ (by simp [hsc, hfp2]; omega)]
    simp only [List.length_take, hsc, show min (S - 8) S = S - 8 by omega, bvm_scr _ S h8S]
    ecancel
  all_goals first
    | trivial | rfl
    | (simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)
    | (show (rcx.toBitVec + 1).toNat = rcx.toNat + 1; simp [BitVec.toNat_add]; omega)


theorem uint8_shr4 (b : UInt8) : b >>> 4 = 0 ↔ b.toNat < 16 := by
  constructor
  · intro h; have := congrArg UInt8.toNat h
    simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow] at this; omega
  · intro h; apply UInt8.toNat_inj.mp; simp [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]; omega

/-- EthLib on a one-byte input: it accepts exactly when no padding bit is set. -/
theorem bv_spec_one (b : UInt8) : deserialize bvDesc #[b] =
    if b.toNat < 16 then .ok (.seq [.bits (unpackBits #[b] 4)]) else .error .paddingBits := by
  simp (config := {decide := true}) [bvDesc, deserialize, deserializeStruct, structSlots, structBudget, readSlots,
    bodyStarts, structBodies, deserializeFields, offsetSpans, Desc.fieldsFixedSize,
    Desc.fixedSize, bind, Except.bind, pure, Except.pure, Functor.map, Except.map, throw, throwThe,
    MonadExceptOf.throw, Slot.held]
  by_cases h : b.toNat < 16
  · simp [h, (uint8_shr4 b).mpr h]
  · simp [h, show ¬ b >>> 4 = 0 from fun e => h ((uint8_shr4 b).mp e)]

-- "J: %w" (types1b.ssz.go, the wrap of the ValidateBitvector error)
def bvFmtJ : List UInt8 := [74, 58, 32, 37, 119]

theorem bvr_a (x c : BitVec 64) : x - 8#64 - 72 + c = x - 80 + c := by bv_omega
theorem bvr_56 (x : BitVec 64) : x - 80 + 56 = x - 24 := by bv_omega
theorem bvr_64 (x : BitVec 64) : x - 80 + 64 = x - 16 := by bv_omega
theorem bvr_fp (x : BitVec 64) : x - 88 - 8 = x - 96 := by bv_omega
theorem bvr_sp (x : BitVec 64) : x - 88 + 8 = x - 80 := by bv_omega
theorem bvr_fr (x : BitVec 64) : x - 88 - 48 = x - 136 := by bv_omega
theorem bvr_rs (x : BitVec 64) : x - 88 - 56 = x - 144 := by bv_omega
theorem bvr_sc (x : BitVec 64) (S : Nat) : x - 88 - 56 - BitVec.ofNat 64 S = x - 144 - BitVec.ofNat 64 S := by bv_omega
theorem bvr_c (x : BitVec 64) : ({ toBitVec := x - 88 } + 8 : UInt64).toBitVec - 8#64 = x - 88 := by
  simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega
theorem bvr_sc' (x : BitVec 64) (S : Nat) :
    x - 88 - BitVec.ofNat 64 (S + 56) + BitVec.ofNat 64 S = x - 144 := by
  have : BitVec.ofNat 64 (S + 56) = BitVec.ofNat 64 S + 56 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
  rw [this]; bv_omega
theorem bvr_join (x : BitVec 64) (S : Nat) (sc rs fr fp : List UInt8) (hsc : sc.length = S) (hrs : rs.length = 8)
    (hfr : fr.length = 40) (hfp : fp.length = 8) (hS : S + 56 < 2 ^ 64) :
    Eq ((sc ++ (rs ++ (fr ++ fp))).At (x - 88 - BitVec.ofNat 64 (S + 56)))
      = Eq (sc.At (x - 144 - BitVec.ofNat 64 S)) ⋆ Eq (rs.At (x - 144)) ⋆ Eq (fr.At (x - 136)) ⋆ Eq (fp.At (x - 96)) := by
  have e : x - 88 - BitVec.ofNat 64 (S + 56) = x - 144 - BitVec.ofNat 64 S := by
    have : BitVec.ofNat 64 (S + 56) = BitVec.ofNat 64 S + 56 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [this]; bv_omega
  rw [e, at_app sc _ (b := x - 144) (by rw [hsc]; bv_omega) (by simp [*]; omega),
    at_app rs _ (b := x - 136) (by rw [hrs]; bv_omega) (by simp [*]),
    at_app fr fp (b := x - 96) (by rw [hfr]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]
theorem bvr_ne (b : UInt8) (h : 16 ≤ b.toNat) : b.toNat >>> 4 ≠ 0 := by
  rw [Nat.shiftRight_eq_div_pow]; omega

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **F1, fixed: the decoder rejects a padding bit.** On `len(buf) = 1` and a
byte `b ≥ 16` (a padding bit set), BitVec.UnmarshalSSZ calls ValidateBitvector
(padding error, `VbvPadC`), wraps it with `fmt.errorf("J: %w")` and returns a
non-nil error. EthLib rejects the same input (`bv_spec_one`). -/
theorem bv_reject_padding_main (k : Nat) (hk : BitVecUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh BitVecUnmarshalSSZ k)
    (b : UInt8) (hb : 16 ≤ b.toNat) (s : MachineData) (ra guard : UInt64)
    (fp s1 s2 a16 rslot spl vfp vfr vrs ity : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (ha16 : a16.length = 16) (hrs : rslot.length = 8)
    (hspl : spl.length = 40) (hvfp : vfp.length = 8) (hvfr : vfr.length = 40) (hvrs : vrs.length = 8)
    (hity : ity.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 16 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (a16.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (spl.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (vfp.At (s.regs.rsp.toBitVec - 96)) ⋆ Eq (vfr.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (vrs.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ Eq (bvFmtJ.At (label "go_string._" + 511).toBitVec)
      ⋆ Eq (vbvFmt.At (label "go_string._" + 27706).toBitVec)
      ⋆ Heap avail ⋆ Eq ([b].At s.regs.rbx.toBitVec) ⋆ R)
    (hguard : guard.toNat + 88 < s.regs.rsp.toNat) (hsp : 144 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 1) (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (hvp : VbvPadC Heap S) (hfe : FmtErrorfC Heap (S + 56)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp
        ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  subst hlen
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; simp only [UInt64.size] at *
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
  rw [bva_s96]
  apply store_step _ _ _ _ _ s2 _ _ (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk BitVecUnmarshalSSZ 8
  kat hk BitVecUnmarshalSSZ 9
  kat hk BitVecUnmarshalSSZ 10
  split
  case isTrue h => exact absurd h (by decide)
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 11
  rw [bva_s88]
  apply store_step _ _ _ _ _ s1 _ _ (by ecancel) (by exact h1)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  kat hk BitVecUnmarshalSSZ 12
  rw [bva_s96]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rbx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk BitVecUnmarshalSSZ 13
  kat hk BitVecUnmarshalSSZ 14
  kat hk BitVecUnmarshalSSZ 15
  kat hk BitVecUnmarshalSSZ 16
  kat hk BitVecUnmarshalSSZ 17
  rw [bva_call]
  apply store_step _ _ _ _ _ rslot _ _ (by ecancel) (by exact hrs)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  rw [← List.take_append_drop 8 spl, at_app (spl.take 8) (spl.drop 8) (b := rsp.toBitVec - 72)
    (by simp [hspl]; bv_omega) (by simp [hspl])] at H5
  refine eventually_trans _ _ _ _ (hvp _ (Host.addrOf (k + 17 + 1)) guard vfp (spl.take 8) vfr vrs [] scratch b avail _
    hvfp (by simp [hspl]) hvfr hvrs hsc hav ?g1 ?g2 ?g3 ?g4 ?g5 ?g6
    (by dsimp only; rw [bvr_fp, bvr_sp, bvr_fr, bvr_rs, List.nil_append]; ecancel)) ?_
  case g1 => dsimp only; show guard.toNat < (rsp.toBitVec - 88).toNat; rw [bva_nat' _ (by omega)]; omega
  case g2 => dsimp only; show 8 ≤ (rsp.toBitVec - 88).toNat; rw [bva_nat' _ (by omega)]; omega
  case g3 => dsimp only; rfl
  case g4 => dsimp only; rfl
  case g5 => dsimp only; simp; decide
  case g6 => dsimp only; exact bvr_ne b hb
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrsp2, hrbp2, hr142, fp2, sp2, fr2, rs2, sc2, obj, hfp2, hsp2, hfr2, hrs2, hsc2,
    hobj, Hm2⟩
  dsimp only at hpc2 hrax2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only [List.nil_append] at hrax2 hrsp2 hrbp2 hr142 Hm2
  subst hrsp2 hrbp2 hr142
  rw [bvr_fp, bvr_sp, bvr_fr, bvr_rs] at Hm2
  kat hk BitVecUnmarshalSSZ 18
  intro _
  kat hk BitVecUnmarshalSSZ 19
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax2, h]; rfl)
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 20
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [bvb, bvr_56]
  apply store_avx_step _ _ _ _ a16 _ _ (by ecancel) (by exact ha16) (by decide)
  intro m6 H6
  kunfold
  rw [lr_split16 _ (Int.toBytes_length 16 _) (rsp.toBitVec - 24)] at H6
  kat hk BitVecUnmarshalSSZ 21
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hit (by rw [← hrax2, h]; rfl)
  simp only [Effects.All]
  kat hk BitVecUnmarshalSSZ 22
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [hrax2])
    (by ecancel) (by exact hity)
  kunfold
  kat hk BitVecUnmarshalSSZ 23
  kat hk BitVecUnmarshalSSZ 24
  rw [bvb, bvr_56]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  kat hk BitVecUnmarshalSSZ 25
  rw [bvb, bvr_64, show rsp.toBitVec - 24 + 8 = rsp.toBitVec - 16 by bv_omega] at *
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel)
    (by simp [Int.toBytes_length])
  intro m8 H8
  simp only [Width.bytes, Width.bits] at H8
  kunfold
  kat hk BitVecUnmarshalSSZ 26
  kat hk BitVecUnmarshalSSZ 27
  kat hk BitVecUnmarshalSSZ 28
  rw [bvb, bvr_56]
  kat hk BitVecUnmarshalSSZ 29
  kat hk BitVecUnmarshalSSZ 30
  kat hk BitVecUnmarshalSSZ 31
  kat hk BitVecUnmarshalSSZ 32
  rw [bvr_c]
  apply store_step _ _ _ _ _ (Int.toBytes 8 (Host.addrOf (k + 17 + 1)).toBitVec.toInt) _ _ (by ecancel)
    (by exact Int.toBytes_length 8 _)
  intro m9 H9
  simp only [Width.bytes, Width.bits] at H9
  kunfold
  have hA : Eq ((Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt ++ Int.toBytes 8 rbx2.toBitVec.toInt).At
      (rsp.toBitVec - 24)) = Eq ((Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt).At (rsp.toBitVec - 24))
      ⋆ Eq ((Int.toBytes 8 rbx2.toBitVec.toInt).At (rsp.toBitVec - 16)) :=
    at_app _ _ (by rw [Int.toBytes_length]; bv_omega) (by simp [Int.toBytes_length])
  have hB := bvr_join rsp.toBitVec S sc2 rs2 fr2 fp2 hsc2 hrs2 hfr2 hfp2 (by omega)
  have hC : Eq ((sp2 ++ spl.drop 8).At (rsp.toBitVec - 88 + 8))
      = Eq (sp2.At (rsp.toBitVec - 80)) ⋆ Eq ((spl.drop 8).At (rsp.toBitVec - 72)) := by
    rw [bvr_sp]; exact at_app _ _ (by rw [hsp2]; bv_omega) (by simp [hsp2, hspl])
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 32 + 1)) (avail - 16) bvFmtJ
    (Int.toBytes 8 (BitVec.ofInt 64 (Int.ofBytes ity)).toInt ++ Int.toBytes 8 rbx2.toBitVec.toInt)
    (sc2 ++ (rs2 ++ (fr2 ++ fp2))) (sp2 ++ spl.drop 8) _ ?f1 ?f2 ?f3 ?f4 ?f5 ?f6
    (by dsimp only; rw [hA, hB, hC]; ecancel)) ?_
  case f1 => dsimp only; rfl
  case f2 => dsimp only; decide
  case f3 => dsimp only
  case f4 => dsimp only; simp [Int.toBytes_length]; decide
  case f5 => simp [hsc2, hrs2, hfr2, hfp2]
  case f6 => simp [hsp2, hspl]
  rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrax3, stk3, sp3, av3, hstk3, hsp3, hav3, Hm3⟩
  dsimp only at hpc3 hrsp3 hr143 hrax3 Hm3
  subst hpc3
  obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
    zmms3, flags3, mem3⟩ := d3
  simp only at hrsp3 hr143 hrax3 Hm3
  subst hrsp3
  kat hk BitVecUnmarshalSSZ 33
  intro _
  kat hk BitVecUnmarshalSSZ 34
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h; exact hrax3 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf BitVecUnmarshalSSZ 43
  kat hk BitVecUnmarshalSSZ 43
  kat hk BitVecUnmarshalSSZ 44
  kat hk BitVecUnmarshalSSZ 45
  rw [bva_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk BitVecUnmarshalSSZ 46
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec from vbv_ret _]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  refine ⟨?_, hrax3, ?_, ?_, sep_true (by ecancel)⟩
  all_goals first
    | rfl
    | (simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64]; done)
    | (apply UInt64.toBitVec_inj.mp; simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]; done)

/-- **Accepted set, EthLib side.** On a one-byte input EthLib accepts exactly
the bytes below 16. With `bv_accept_main` (b < 16 → nil) and
`bv_reject_padding_main` (16 ≤ b → non-nil error) the machine code accepts
exactly the same bytes (F1 fixed); `bv_reject_size_main` covers `len ≠ 1`. -/
theorem bv_spec_accepts_iff (b : UInt8) : (∃ v, deserialize bvDesc #[b] = .ok v) ↔ b.toNat < 16 := by
  rw [bv_spec_one]
  by_cases h : b.toNat < 16 <;> simp [h]
