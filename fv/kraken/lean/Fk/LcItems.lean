import Fk.LcOrder
import Fk.LuReject

/-!
# ListC.UnmarshalSSZ, element decode error (fix 3 X5, review fix3-r1 M4)

One element whose bytes are too short for a ListU64 (fewer than 4): the
element decoder `ListU64.UnmarshalSSZ` returns `ssz.ErrSize` (an initialized
`*errors.errorString` global) and the ListC decoder wraps it with
`fmt.Errorf("Items: %w", err)` (format `Fk.Data.lcFmtItems`, contract
`FmtErrorfWC`).

`lu_reject_short_frame` is `lu_reject_short_main` with a conclusion that keeps
the callee's stack slots, r14 and the error global (the statement of
`lu_reject_short_main` is unchanged). `LuURejShortC` is the function
specification of that path; `lu_urej_short_holds` derives it from the machine
code.
-/

open Fk Fk.Code Fv1 EthLib.Serialization.Ssz
variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `lu_reject_short_main` with the frame kept: the return slot, the saved
rbp slot and the spill slot (new bytes of the same length), the guard, the
two words of `ssz.ErrSize`, r14. -/
theorem lu_reject_short_frame (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp slot : List UInt8) (hfp : fp.length = 8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat - 8) (hsp : 8 ≤ s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat < 4) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ ∃ fp' slot' : List UInt8, fp'.length = 8 ∧ slot'.length = 8 ∧
        (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq (fp'.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (slot'.At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kat hk ListU64UnmarshalSSZ 0
  kat hk ListU64UnmarshalSSZ 1
  kat hk ListU64UnmarshalSSZ 2
  kat hk ListU64UnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg8 _ (by simpa using hsp)]; simpa using hguard)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListU64UnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by kaddr) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListU64UnmarshalSSZ 6
  kat hk ListU64UnmarshalSSZ 7
  kat hk ListU64UnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lu_neg8 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListU64UnmarshalSSZ 9
  kat hk ListU64UnmarshalSSZ 10
  kat hk ListU64UnmarshalSSZ 11
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  klabel hk hf ListU64UnmarshalSSZ 137
  kat hk ListU64UnmarshalSSZ 137
  kat hk ListU64UnmarshalSSZ 138
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 139
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 140
  kat hk ListU64UnmarshalSSZ 141
  rw [lu_pop]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListU64UnmarshalSSZ 142
  rw [show rsp.toBitVec - 8 + 8#64 = rsp.toBitVec by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, ?_, ?_, ?_, ?_, trivial, Int.toBytes 8 rbp.toBitVec.toInt, Int.toBytes 8 rbx.toBitVec.toInt,
    Int.toBytes_length 8 _, Int.toBytes_length 8 _, ?_⟩
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · apply UInt64.toBitVec_inj.mp; simp
  · first | trivial | rfl
  · ecancel

/-- ListU64.UnmarshalSSZ, short input (`len(buf) < 4`): it returns the two
words of `ssz.ErrSize` (rax, rbx). Frame like `LuUAccC`: a `144 + S`-byte stack
block below the return slot and the spill slot at rsp + 16; the global words,
the guard and `F` are kept. -/
def LuURejShortC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (stk sp2 : List UInt8) (guard e0 e1 : UInt64) (F : DataMem → Prop),
    stk.length = 144 + S → sp2.length = 8 → st.regs.rcx.toNat < 4 →
    guard.toNat < st.regs.rsp.toNat - 8 → 8 ≤ st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = e0 ∧ st'.data.regs.rbx = e1
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ stk' sp2' : List UInt8, stk'.length = 144 + S ∧ sp2'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ Eq (sp2'.At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "target.ListU64.UnmarshalSSZ"⟩

theorem luShort_split (stk : List UInt8) (S : Nat) (hS : S < 2 ^ 60) (h : stk.length = 144 + S) (x : BitVec 64) :
    Eq (stk.At (x - 144 - BitVec.ofNat 64 S)) = Eq ((stk.take (136 + S)).At (x - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((stk.drop (136 + S)).At (x - 8)) := by
  conv => lhs; rw [← List.take_append_drop (136 + S) stk]
  exact at_app _ _ (by
    simp only [List.length_take, h, show min (136 + S) (144 + S) = 136 + S by omega]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega) (by simp [h]; omega)

set_option maxHeartbeats 8000000 in
/-- The ListU64 machine code satisfies `LuURejShortC` (from `lu_reject_short_frame`). -/
theorem lu_urej_short_holds (k : Nat) (hk : ListU64UnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListU64UnmarshalSSZ k) (S : Nat) (hS : S < 2 ^ 60) : LuURejShortC S := by
  intro st ret stk sp2 guard e0 e1 F hstk hsp2 hlen hguard hsp hm
  rw [label_at hk hf (j := 0) (l := "target.ListU64.UnmarshalSSZ") (by rfl) (by intro i hi; omega)]
  rw [luShort_split stk S hS hstk] at hm
  refine eventually_trans _ _ _ _ (lu_reject_short_frame k hk hf st (UInt64.ofBitVec ret.toBitVec) guard e0 e1
    (stk.drop (136 + S)) sp2 (by simp [hstk]; omega) hsp2
    (Eq ((stk.take (136 + S)).At (st.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 S)) ⋆ F) (by ecancel) hguard hsp hlen) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrsp, -, hr14, fp', sl', hfp', hsl', hmem⟩
  refine Eventually.done _ ⟨hpc, hrax, hrbx, hrsp, hr14, stk.take (136 + S) ++ fp', sl',
    by simp [hstk, hfp']; omega, hsl', ?_⟩
  rw [luShort_split _ S hS (by simp [hstk, hfp']; omega),
    List.take_left' (by simp [hstk]), List.drop_left' (by simp [hstk])]
  ecancel

theorem lcFmtItems_len : lcFmtItems.length = 9 := by rfl

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- The last element loop iteration `i` with a too-short element (`e − s < 4`
bytes): the element decoder returns `ssz.ErrSize` (`LuURejShortC`; its first
word is the errorString itab), and the reject block (343–370) wraps it with
`fmt.errorf("Items: %w", err)` (`FmtErrorfWC` with `lcFmtItems`) and returns a
non-nil error. The block uses the 16-byte argument array at `x − 120` and the
callee spill area `x − 224 .. x − 184` (premises here). -/
theorem lcl_itemerr (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (x base recv A : BitVec 64) (tl ptrs : List UInt8) (T n i s e : Nat)
    (hT : tl.length = T) (hn : n ≤ 4) (hi : i < n) (hl' : i + 1 = n) (hptrs : ptrs.length = 8 * i)
    (hse : s < e) (heT : e ≤ T) (hshort : e - s < 4) (hs4 : 4 * n ≤ s)
    (hlast : i + 1 = n → e = T)
    (hT32 : T < 2 ^ 32) (cap0 : Nat) (hcap : T + 4 ≤ cap0) (hcap63 : cap0 < 2 ^ 63)
    (S : Nat) (hS : S < 2 ^ 60) (blk rslot sp1 sp2 sp3 s200 s192 s136 s152 s160 s184 b0 : List UInt8)
    (hblk : blk.length = 144 + S) (hrs : rslot.length = 8) (hsp1 : sp1.length = 8) (hsp2 : sp2.length = 8)
    (hsp3 : sp3.length = 8) (h200 : s200.length = 8) (h192 : s192.length = 8)
    (h136 : s136.length = 8) (h152 : s152.length = 8) (h160 : s160.length = 8) (h184 : s184.length = 8)
    (hb0 : b0.length = 16)
    (ra rbp0 guard e0 e1 : UInt64) (ity msg hm : List UInt8) (sp : BitVec 64) (hity : ity.length = 8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (RO : DataMem → Prop) (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (hmsg : MsgIn sp msg hm)
    (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 24 + 9 + msg.length + 8192 ≤ avail)
    (O R : DataMem → Prop) (s0 : MachineData)
    (hrax : s0.regs.rax.toNat = i) (hrdx : s0.regs.rdx.toNat = n) (hrcx : s0.regs.rcx.toNat = s)
    (hrsp : s0.regs.rsp.toBitVec = x - 8#64 - 216)
    (hguard : guard.toNat + 400 + S < x.toNat) (hx : 400 + S ≤ x.toNat)
    (h_mem : s0.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At x) ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At (x - 8))
      ⋆ Eq ((Int.toBytes 8 recv.toInt).At (x + 8))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt).At (x + 32))
      ⋆ Eq ((Int.toBytes 8 base.toInt).At (x - 128)) ⋆ Eq (s136.At (x - 136))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt).At (x - 144))
      ⋆ Eq (s152.At (x - 152)) ⋆ Eq (s160.At (x - 160))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (x - 168))
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 T).toInt).At (x - 176))
      ⋆ Eq (s184.At (x - 184))
      ⋆ Eq (sp1.At (x - 224)) ⋆ Eq (sp2.At (x - 216)) ⋆ Eq (rslot.At (x - 232))
      ⋆ Eq (blk.At (x - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s0.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq (tl.At base)
      ⋆ Eq ((Int.toBytes 8 A.toInt).At recv) ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (recv + 8))
      ⋆ Eq ((ptrs ++ List.replicate (8 * (n - i)) 0).At A)
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (sp3.At (x - 208)) ⋆ Eq (s200.At (x - 200)) ⋆ Eq (s192.At (x - 192))
      ⋆ Eq (b0.At (x - 120)) ⋆ Eq (lcFmtItems.At lcFmtItems_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrObj e1.toBitVec sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ O ⋆ R)
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hlu : LuURejShortC S) (hfe : FmtErrorfWC Heap lcFmtItems RO MsgIn (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp.toBitVec = x + 8 ∧ st.data.regs.rbp = rbp0 ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s0, Host.addrOf (k + 239)⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s0
  simp only at h_mem hrax hrdx hrcx hrsp ⊢
  have := rax.toNat_lt_size; have := rdx.toNat_lt_size; have := rcx.toNat_lt_size; have := x.isLt
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 239
  kat hk ListCUnmarshalSSZ 240
  kat hk ListCUnmarshalSSZ 241
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 242
  rw [show rsp.toBitVec + 64 = x - 160 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ s160 _ _ (by ecancel) (by exact h160)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 243
  rw [show rsp.toBitVec + 40 = x - 184 by rw [hrsp]; bv_omega]
  apply store_step _ _ _ _ _ s184 _ _ (by ecancel) (by exact h184)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 244
  kat hk ListCUnmarshalSSZ 245
  kat hk ListCUnmarshalSSZ 246
  apply store_step_at _ _ (x - 232) _ _ _ rslot _ _ (by rw [hrsp, lcl_ret]) (by ecancel) (by exact hrs)
  intro m3 H3
  simp only [Width.bytes, Width.bits] at H3
  kunfold
  rw [show rsp.toBitVec - 8#64 = x - 232 by rw [hrsp, lcl_ret]] at *
  have hspA : x - 232 + 8 = x - 224 := by bv_omega
  refine eventually_trans _ _ _ _ (hno _ (Host.addrOf (k + 246 + 1)) avail blk sp1 _ rfl (by omega) hblk hsp1
    (by dsimp only; rw [lcl_blk, hspA]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sn1, hstk1, hsn1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [lcl_blk, luObj_sep, hspA] at Hm1
  kat hk ListCUnmarshalSSZ 247
  rw [lcl_g, show x - 224 + 64 = x - 160 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 248
  kat hk ListCUnmarshalSSZ 249
  rw [lcl_g, show x - 224 + 56 = x - 168 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 250
  kat hk ListCUnmarshalSSZ 251
  have hi1 : (rax.toBitVec + 1).toNat = i + 1 := by simp [BitVec.toNat_add]; omega
  have hl : i + 1 = n := hl'
  have heq := hlast hl
  subst heq
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply h; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 268
  kat hk ListCUnmarshalSSZ 268
  kat hk ListCUnmarshalSSZ 269
  rw [lcl_g, show x - 224 + 80 = x - 144 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (cap0 - 4)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 270
  kat hk ListCUnmarshalSSZ 271
  rw [lcl_g, show x - 224 + 48 = x - 176 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 e).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 272
  kat hk ListCUnmarshalSSZ 273
  rw [lcl_g, show x - 224 + 96 = x - 128 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 base.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 274
  kat hk ListCUnmarshalSSZ 275
  rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 276
  kat hk ListCUnmarshalSSZ 277
  rw [jb_false _ _ _ _ (by simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 278
  kat hk ListCUnmarshalSSZ 279
  kat hk ListCUnmarshalSSZ 280
  rw [ja_false _ _ _ _ (by simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 281
  rw [lcl_g, show x - 224 + 88 = x - 136 by bv_omega]
  apply store_step _ _ _ _ _ s136 _ _ (by ecancel) (by exact h136)
  intro m4 H4
  simp only [Width.bytes, Width.bits] at H4
  kunfold
  kat hk ListCUnmarshalSSZ 282
  rw [lcl_g, show x - 224 + 72 = x - 152 by bv_omega]
  apply store_step _ _ _ _ _ s152 _ _ (by ecancel) (by exact h152)
  intro m5 H5
  simp only [Width.bytes, Width.bits] at H5
  kunfold
  kat hk ListCUnmarshalSSZ 283
  rw [lcl_g, show x - 224 + 40 = x - 184 by bv_omega]
  apply store_step _ _ _ _ _ (Int.toBytes 8 rcx.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m6 H6
  simp only [Width.bytes, Width.bits] at H6
  kunfold
  kat hk ListCUnmarshalSSZ 284
  rw [lcl_g, show x - 224 + 256 = x + 32 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 cap0).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 285
  kat hk ListCUnmarshalSSZ 286
  kat hk ListCUnmarshalSSZ 287
  kat hk ListCUnmarshalSSZ 288
  kat hk ListCUnmarshalSSZ 289
  kat hk ListCUnmarshalSSZ 290
  kat hk ListCUnmarshalSSZ 291
  kat hk ListCUnmarshalSSZ 292
  kshl64 63
  kat hk ListCUnmarshalSSZ 293
  intro _
  kat hk ListCUnmarshalSSZ 294
  kat hk ListCUnmarshalSSZ 295
  have hrcx' : rcx.toBitVec = BitVec.ofNat 64 s := by apply BitVec.eq_of_toNat_eq; simp; omega
  have hy : (BitVec.ofNat 64 cap0 - rcx.toBitVec + -4).toNat = cap0 - s - 4 := by
    rw [hrcx']; exact lcl_y cap0 s (by omega) hcap63
  rw [lc_mask _ _ (by rw [hy]; omega) (by rw [hy]; omega)]
  rw [show rcx.toBitVec + base * 1#64 = base + BitVec.ofNat 64 s by rw [hrcx', BitVec.mul_one, BitVec.add_comm]]
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 246 + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m7 H7
  simp only [Width.bytes, Width.bits] at H7
  kunfold
  rw [lcl_call] at *
  have hx232 : (x - 232).toNat = x.toNat - 232 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp
  refine eventually_trans _ _ _ _ (hlu _ (Host.addrOf (k + 295 + 1)) stk1 sp2 guard e0 e1 _ hstk1 hsp2
    (by show (BitVec.ofNat 64 e - rcx.toBitVec).toNat < 4; rw [hrcx']; simp [BitVec.toNat_sub]; omega)
    (by show guard.toNat < (x - 232).toNat - 8; rw [hx232]; omega)
    (by show 8 ≤ (x - 232).toNat; rw [hx232]; omega)
    (by dsimp only; rw [show x - 232 + 16 = x - 216 by bv_omega]; ecancel)) ?_
  have he0' : e0 ≠ 0 := fun h => hit (by rw [← he0, h]; rfl)
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hr142, stk2, sp2', hstk2, hsp2', Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hr142 Hm2
  subst hrax2 hrbx2 hrsp2
  rw [show x - 232 + 16 = x - 216 by bv_omega] at Hm2
  kat hk ListCUnmarshalSSZ 296
  intro _
  kat hk ListCUnmarshalSSZ 297
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0' (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 343
  kat hk ListCUnmarshalSSZ 343
  kat hk ListCUnmarshalSSZ 344
  simp only [AvxOperation.interp, MachineData.setAvxLegacy, AvxRegOrMem.interp]
  kunfold
  rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega]
  apply store_avx_step _ _ _ _ b0 _ _ (by ecancel) (by exact hb0) (by decide)
  intro m8 H8
  kunfold
  kat hk ListCUnmarshalSSZ 345
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact he0' (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 346
  apply load_step_at _ _ ((label "go_itab._errors.errorString_error").toBitVec + 8) _ _ ity _ _ (by rw [he0])
    (by ecancel) (by exact hity)
  kunfold
  kat hk ListCUnmarshalSSZ 347
  kat hk ListCUnmarshalSSZ 348
  rw [lr_split16 _ (Int.toBytes_length 16 _) (x - 120)] at H8
  rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).take 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m9 H9
  simp only [Width.bytes, Width.bits, toBytes_ofInt_ofBytes 64 8 rfl ity hity] at H9
  kunfold
  kat hk ListCUnmarshalSSZ 349
  rw [lcl_g, show x - 224 + 112 = x - 120 + 8 by bv_omega]
  apply store_step _ _ _ _ _ ((Int.toBytes 16 (zmms2.get (AvxReg.xmm RegMm.mm15)).toInt).drop 8) _ _ (by ecancel) (by simp [Int.toBytes_length])
  intro m10 H10
  simp only [Width.bytes, Width.bits] at H10
  kunfold
  kat hk ListCUnmarshalSSZ 350
  kat hk ListCUnmarshalSSZ 351
  kat hk ListCUnmarshalSSZ 352
  kat hk ListCUnmarshalSSZ 353
  kat hk ListCUnmarshalSSZ 354
  kat hk ListCUnmarshalSSZ 355
  apply store_step_at _ _ (x - 232) _ _ _ (Int.toBytes 8 (Host.addrOf (k + 295 + 1)).toBitVec.toInt) _ _
    (lcl_call _) (by ecancel) (by exact Int.toBytes_length 8 _)
  intro m11 H11
  simp only [Width.bytes, Width.bits] at H11
  kunfold
  rw [lcl_call] at *
  try simp only [lcFmtItems_addr] at H11
  refine eventually_trans _ _ _ _ (hfe _ (Host.addrOf (k + 355 + 1)) (avail - 24) ity msg hm stk2
    (sn1 ++ (sp2' ++ (sp3 ++ (s200 ++ s192)))) rbx2.toBitVec sp _
    (by rw [lcFmtItems_len]; rfl) (by first | rfl | decide) (by first | rfl | decide) hity hmsg hstk2
    (by simp [hsn1, hsp2', hsp3, h200, h192]) (by rw [lcFmtItems_len]; omega)
    (by dsimp only
        rw [lcl_g, show x - 224 + 104 = x - 120 by bv_omega,
          at_app sn1 _ (b := x - 216) (by rw [hsn1]; bv_omega) (by simp [hsn1, hsp2', hsp3, h200, h192]),
          join4 (x - 216) (x - 208) (x - 200) (x - 192) _ _ _ _ hsp2' hsp3 h200 h192 (by bv_omega) (by bv_omega) (by bv_omega),
          at_app ity _ (b := x - 120 + 8) (by rw [hity]; bv_omega) (by simp [hity, Int.toBytes_length]),
          hspA, lcl_blk]
        ecancel)) ?_
  rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrax4, stk4, sp4, av4, hstk4, hsp4, hav4, Hm4⟩
  dsimp only at hpc4 hrsp4 hrax4 Hm4
  subst hpc4
  obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
    zmms4, flags4, mem4⟩ := d4
  simp only at hrsp4 hrax4 Hm4
  subst hrsp4
  kat hk ListCUnmarshalSSZ 356
  intro _
  kat hk ListCUnmarshalSSZ 357
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    exact hrax4 (UInt64.toBitVec_inj.mp (by simpa using h))
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 367
  kat hk ListCUnmarshalSSZ 367
  kat hk ListCUnmarshalSSZ 368
  kat hk ListCUnmarshalSSZ 369
  rw [show (216 : BitVec 64) + ({ toBitVec := x - 232 } + 8 : UInt64).toBitVec = x - 8 by
    simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rbp0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 370
  rw [show x - 8 + 8#64 = x by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨trivial, hrax4, ?_, ?_, ?_⟩
  · first | (simp; done) | (simp; bv_omega)
  · first | trivial | rfl | (apply UInt64.toBitVec_inj.mp; simp)
  · exact sep_true (by ecancel)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 200000 in
/-- **ListC element decode error** (fix 3 X5, review fix3-r1 M4). Input
`buf = offset 4 ‖ tl` with one element (`n = 1`, first offset 4) whose bytes
are too short for a ListU64 (`4 < T < 8`: 1–3 bytes). The decoder allocates the
element slice and the element, calls `ListU64.UnmarshalSSZ` on the element
bytes, which returns `ssz.ErrSize` (`LuURejShortC`, derived from the machine
code by `lu_urej_short_holds`), and returns `fmt.Errorf("Items: %w", err)`: a
non-nil error. The error global is initialized (`he0`, `hit`, `ity` at the
itab's type word, `ErrObj e1 sp msg`). Premises beyond `lc_accept_main`'s
frame: the argument array (`rsp − 120`, 16 bytes), the spill slots
`rsp − 200`, `rsp − 192`, the format bytes. -/
theorem lc_reject_item_main (k : Nat) (hk : ListCUnmarshalSSZ.IsInfixAt Host.prog k)
    (hf : LabelsFresh ListCUnmarshalSSZ k)
    (tl : List UInt8) (T n : Nat) (hT : tl.length = T) (hn1 : n = 1) (hn : n ≤ 4) (hT32 : T < 2 ^ 32)
    (hle4n : 4 * n < T) (hshort : T < 8)
    (hfirst : tl.take 4 = (uintBytes 4 (4 * n)).toList)
    (s : MachineData) (ra guard : UInt64) (fp slot s8 s32 l128 l136 l144 l152 l160 l168 l176 l184 l192 l200 l208 l216 l224
      rslot blk cP cL cC b0 : List UInt8)
    (hfp : fp.length = 8) (hsl : slot.length = 8) (h8 : s8.length = 8) (h32 : s32.length = 8)
    (hl128 : l128.length = 8) (hl136 : l136.length = 8) (hl144 : l144.length = 8) (hl152 : l152.length = 8)
    (hl160 : l160.length = 8) (hl168 : l168.length = 8) (hl176 : l176.length = 8) (hl184 : l184.length = 8)
    (hl192 : l192.length = 8) (hl200 : l200.length = 8)
    (hl208 : l208.length = 8) (hl216 : l216.length = 8) (hl224 : l224.length = 8) (hrs : rslot.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hb0 : b0.length = 16)
    (S : Nat) (hS : S < 2 ^ 60) (hblk : blk.length = 144 + S)
    (e0 e1 : UInt64) (ity msg hm : List UInt8) (sp : BitVec 64) (hity : ity.length = 8)
    (he0 : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0)
    (RO : DataMem → Prop) (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (hmsg : MsgIn sp msg hm)
    (R : DataMem → Prop) (Heap : Nat → DataMem → Prop) (avail : Nat) (hav : 32 + 24 + 9 + msg.length + 8192 ≤ avail)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s8.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16)) ⋆ Eq (s32.At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq (l128.At (s.regs.rsp.toBitVec - 128)) ⋆ Eq (l136.At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq (l144.At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (l152.At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq (l160.At (s.regs.rsp.toBitVec - 160)) ⋆ Eq (l168.At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq (l176.At (s.regs.rsp.toBitVec - 176)) ⋆ Eq (l184.At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq (l224.At (s.regs.rsp.toBitVec - 224)) ⋆ Eq (l216.At (s.regs.rsp.toBitVec - 216))
      ⋆ Eq (l208.At (s.regs.rsp.toBitVec - 208))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 232)) ⋆ Eq (blk.At (s.regs.rsp.toBitVec - 232 - 144 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ Heap avail
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((tl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq (l200.At (s.regs.rsp.toBitVec - 200)) ⋆ Eq (l192.At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq (b0.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (lcFmtItems.At lcFmtItems_addr)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrObj e1.toBitVec sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ R)
    (hguard : guard.toNat + 400 + S < s.regs.rsp.toNat) (hsp : 400 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx.toNat = 4 + T) (hcap : s.regs.rcx.toNat ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
    (hms : MakesliceC Heap (label "type__" + 114368).toBitVec 8 (144 + S))
    (hno : NewobjectC Heap (label "type__" + 83104).toBitVec 24 (144 + S))
    (hlu : LuURejShortC S) (hfe : FmtErrorfWC Heap lcFmtItems RO MsgIn (144 + S)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax ≠ 0
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ (R ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  have hT4 : 4 ≤ T := by omega
  have ho4 : (tl.take 4).length = 4 := by simp; omega
  have hoff : Int.ofBytes (tl.take 4) = ((4 * n : Nat) : Int) := by
    rw [hfirst, ofBytes_uintBytes4 _ (by omega)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hguard hsp hlen hcap hcap63 ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; have := rdi.toNat_lt_size
  simp only [UInt64.size] at *
  kat hk ListCUnmarshalSSZ 0
  kat hk ListCUnmarshalSSZ 1
  kat hk ListCUnmarshalSSZ 2
  kat hk ListCUnmarshalSSZ 3
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hk ListCUnmarshalSSZ 4
  split
  case isTrue h =>
    exfalso
    rw [cmp_be_false _ _ _ _ (by rw [toNat_add_neg96 _ (by simp; omega)]; simp; omega)] at h
    exact absurd h (by simp)
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 5
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hk ListCUnmarshalSSZ 6
  kat hk ListCUnmarshalSSZ 7
  kat hk ListCUnmarshalSSZ 8
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ slot _ _ (lc_s16 _) (by ecancel) (by exact hsl)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kat hk ListCUnmarshalSSZ 9
  kat hk ListCUnmarshalSSZ 10
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 11
  apply load_step_at _ _ rbx.toBitVec _ _ [4, 0, 0, 0] _ _ (by bv_omega) (by ecancel) (by simp)
  simp only [show Int.ofBytes [4, 0, 0, 0] = 4 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 12
  kat hk ListCUnmarshalSSZ 13
  kat hk ListCUnmarshalSSZ 14
  kat hk ListCUnmarshalSSZ 15
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 16
  kat hk ListCUnmarshalSSZ 17
  kat hk ListCUnmarshalSSZ 18
  kat hk ListCUnmarshalSSZ 19
  kshl64 63
  kat hk ListCUnmarshalSSZ 20
  intro _
  rw [lc_rdx4 _ (by simp; omega) (by simp; omega)]
  kat hk ListCUnmarshalSSZ 21
  kat hk ListCUnmarshalSSZ 22
  kat hk ListCUnmarshalSSZ 23
  kat hk ListCUnmarshalSSZ 24
  kat hk ListCUnmarshalSSZ 25
  kat hk ListCUnmarshalSSZ 26
  kat hk ListCUnmarshalSSZ 27
  rw [jle3_false _ _ (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)
    (by rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega)]; simp; omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 28
  apply load_step_at _ _ (rbx.toBitVec + 4) _ _ (tl.take 4) _ _ (by bv_omega) (by ecancel) (by exact ho4)
  rw [hoff]
  kunfold
  kat hk ListCUnmarshalSSZ 29
  kat hk ListCUnmarshalSSZ 30
  kat hk ListCUnmarshalSSZ 31
  intro _
  have ho32 : 4 * n < 2 ^ 32 := by
    omega
  rw [zx_o (4 * n) ho32]
  kat hk ListCUnmarshalSSZ 32
  split
  case isTrue h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    have := congrArg BitVec.toNat h; simp at this; omega
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 33
  kat hk ListCUnmarshalSSZ 34
  intro _
  rw [and3_zero (4 * n) ho32 (by omega)]
  kat hk ListCUnmarshalSSZ 35
  split
  case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  kat hk ListCUnmarshalSSZ 36
  kat hk ListCUnmarshalSSZ 37
  kshl64 2
  rw [shr2_o (4 * n) ho32]
  kat hk ListCUnmarshalSSZ 38
  kat hk ListCUnmarshalSSZ 39
  rw [ja4_false _ (by omega)]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hk ListCUnmarshalSSZ 40
  kat hk ListCUnmarshalSSZ 41
  kat hk ListCUnmarshalSSZ 42
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add] at h; omega
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 64
  kat hk ListCUnmarshalSSZ 64
  kat hk ListCUnmarshalSSZ 65
  rw [show rsp.toBitVec - 8#64 - 216 + 232 = rsp.toBitVec + 8 by bv_omega]
  apply store_step _ _ _ _ _ s8 _ _ (by ecancel) (by exact h8)
  intro n1 N1
  simp only [Width.bytes, Width.bits] at N1
  kunfold
  kat hk ListCUnmarshalSSZ 66
  rw [show rsp.toBitVec - 8#64 - 216 + 48 = rsp.toBitVec - 176 by bv_omega]
  apply store_step _ _ _ _ _ l176 _ _ (by ecancel) (by exact hl176)
  intro n2 N2
  simp only [Width.bytes, Width.bits] at N2
  kunfold
  kat hk ListCUnmarshalSSZ 67
  rw [show rsp.toBitVec - 8#64 - 216 + 80 = rsp.toBitVec - 144 by bv_omega]
  apply store_step _ _ _ _ _ l144 _ _ (by ecancel) (by exact hl144)
  intro n3 N3
  simp only [Width.bytes, Width.bits] at N3
  kunfold
  kat hk ListCUnmarshalSSZ 68
  rw [show rsp.toBitVec - 8#64 - 216 + 96 = rsp.toBitVec - 128 by bv_omega]
  apply store_step _ _ _ _ _ l128 _ _ (by ecancel) (by exact hl128)
  intro n4 N4
  simp only [Width.bytes, Width.bits] at N4
  kunfold
  kat hk ListCUnmarshalSSZ 69
  rw [show rsp.toBitVec - 8#64 - 216 + 56 = rsp.toBitVec - 168 by bv_omega]
  apply store_step _ _ _ _ _ l168 _ _ (by ecancel) (by exact hl168)
  intro n5 N5
  simp only [Width.bytes, Width.bits] at N5
  kunfold
  kat hk ListCUnmarshalSSZ 70
  rw [show rsp.toBitVec - 8#64 - 216 + 256 = rsp.toBitVec + 32 by bv_omega]
  apply store_step _ _ _ _ _ s32 _ _ (by ecancel) (by exact h32)
  intro n7 N7
  simp only [Width.bytes, Width.bits] at N7
  kunfold
  kat hk ListCUnmarshalSSZ 71
  rw [show rsp.toBitVec - 8#64 - 216 + 72 = rsp.toBitVec - 152 by bv_omega]
  apply store_step _ _ _ _ _ l152 _ _ (by ecancel) (by exact hl152)
  intro n6 N6
  simp only [Width.bytes, Width.bits] at N6
  kunfold
  kat hk ListCUnmarshalSSZ 72
  kat hk ListCUnmarshalSSZ 73
  kat hk ListCUnmarshalSSZ 74
  kat hk ListCUnmarshalSSZ 75
  apply store_step_at _ _ (rsp.toBitVec - 232) _ _ _ rslot _ _ (lcl_ret _) (by ecancel) (by exact hrs)
  intro n8 N8
  simp only [Width.bytes, Width.bits] at N8
  kunfold
  rw [lcl_ret] at *
  have hn4 : 4 * n / 4 = n := by omega
  rw [hn4]
  have hsp3 : ∀ (a b c : List UInt8), a.length = 8 → b.length = 8 → c.length = 8 →
      Eq ((a ++ (b ++ c)).At (rsp.toBitVec - 232 + 8)) = Eq (a.At (rsp.toBitVec - 224)) ⋆ Eq (b.At (rsp.toBitVec - 216))
        ⋆ Eq (c.At (rsp.toBitVec - 208)) := by
    intro a b c ha hb hc
    rw [at_app a _ (b := rsp.toBitVec - 216) (by rw [ha]; bv_omega) (by simp [*]),
      at_app b c (b := rsp.toBitVec - 208) (by rw [hb]; bv_omega) (by simp [*]), show rsp.toBitVec - 232 + 8 = rsp.toBitVec - 224 by bv_omega]
    simp only [Std.ExtHashMap.sep_assoc]
  refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (k + 75 + 1)) n avail blk (l224 ++ (l216 ++ l208)) _ rfl
    (by show (BitVec.ofNat 64 n).toNat ≤ _; simp; omega)
    (by show (BitVec.ofNat 64 n).toNat = _; simp; omega) (by omega) (by unfold maxAlloc; omega) (by omega) hblk
    (by simp [*]) (by dsimp only; rw [lcl_blk, hsp3 _ _ _ hl224 hl216 hl208]; ecancel)) ?_
  rintro ⟨d1, pc1⟩ ⟨hpc1, hrsp1, hr141, -, stk1, sm1, hstk1, hsm1, Hm1⟩
  dsimp only at hpc1 hrsp1 hr141 Hm1
  subst hpc1
  obtain ⟨⟨rax1, rbx1, rcx1, rdx1, rsi1, rdi1, rsp1, rbp1, r81, r91, r101, r111, r121, r131, r141, r151⟩,
    zmms1, flags1, mem1⟩ := d1
  simp only at hrsp1 hr141 Hm1
  subst hrsp1 hr141
  rw [lcl_blk, hn4, ← List.take_append_drop 8 sm1, ← List.take_append_drop 8 (sm1.drop 8),
    hsp3 _ _ _ (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1])] at Hm1
  kat hk ListCUnmarshalSSZ 76
  rw [lcl_g, show rsp.toBitVec - 224 + 56 = rsp.toBitVec - 168 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 n).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 77
  rw [lcl_g, show rsp.toBitVec - 224 + 232 = rsp.toBitVec + 8 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 rax.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 78
  apply store_step_at _ _ (rax.toBitVec + 8) _ _ _ cL _ _ (by bv_omega) (by ecancel) (by exact hcL)
  intro n9 N9
  simp only [Width.bytes, Width.bits] at N9
  kunfold
  kat hk ListCUnmarshalSSZ 79
  apply store_step_at _ _ (rax.toBitVec + 16) _ _ _ cC _ _ (by bv_omega) (by ecancel) (by exact hcC)
  intro n10 N10
  simp only [Width.bytes, Width.bits] at N10
  kunfold
  kat hk ListCUnmarshalSSZ 80
  apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
  simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
  kunfold
  kat hk ListCUnmarshalSSZ 81
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  klabel hk hf ListCUnmarshalSSZ 86
  kat hk ListCUnmarshalSSZ 86
  kat hk ListCUnmarshalSSZ 87
  apply store_step_at _ _ rax.toBitVec _ _ _ cP _ _ (by bv_omega) (by ecancel) (by exact hcP)
  intro n11 N11
  simp only [Width.bytes, Width.bits] at N11
  kunfold
  kat hk ListCUnmarshalSSZ 88
  intro _
  kat hk ListCUnmarshalSSZ 89
  rw [lcl_g, show rsp.toBitVec - 224 + 72 = rsp.toBitVec - 152 by bv_omega]
  apply load_step _ _ _ _ (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  kunfold
  kat hk ListCUnmarshalSSZ 90
  intro _
  kat hk ListCUnmarshalSSZ 91
  intro _
  kat hk ListCUnmarshalSSZ 92
  klabel hk hf ListCUnmarshalSSZ 239
  have hrcx4 : 4 ≤ rcx.toNat := by omega
  have hrdi4 : 4 ≤ rdi.toNat := by omega
  rw [lca_m4 _ (by simpa using hrdi4), lca_m4' _ (by simpa using hrcx4), BitVec.mul_one,
    show rcx.toBitVec.toNat - 4 = T by simp; omega] at N11
  rw [show Int.toBytes 8 rdi.toBitVec.toInt = Int.toBytes 8 (BitVec.ofNat 64 rdi.toBitVec.toNat).toInt by simp] at N11
  have htl : Eq (tl.At (rbx.toBitVec + 4)) = Eq ((tl.take 4).At (rbx.toBitVec + 4))
      ⋆ Eq ((tl.drop 4).At (rbx.toBitVec + 4 + 4)) := by
    conv => lhs; rw [← List.take_append_drop 4 tl]
    exact at_app _ _ (by rw [List.length_take, Nat.min_eq_left (by omega)]; rfl) (by simp; omega)
  refine eventually_trans _ _ _ _ (lcl_itemerr k hk hf rsp.toBitVec (rbx.toBitVec + 4) rax.toBitVec rax1.toBitVec tl []
    T n 0 (4 * n) T hT hn (by omega) (by omega) rfl (by omega) (Nat.le_refl _) (by omega) (Nat.le_refl _) (fun _ => rfl)
    hT32 rdi.toBitVec.toNat (by simp; omega) (by simpa using hcap63) S hS stk1
    (Int.toBytes 8 (Host.addrOf (k + 75 + 1)).toBitVec.toInt) (sm1.take 8) ((sm1.drop 8).take 8) ((sm1.drop 8).drop 8)
    l200 l192 l136 (Int.toBytes 8 (BitVec.ofNat 64 (4 * n)).toInt) l160 l184 b0
    hstk1 (Int.toBytes_length 8 _) (by simp [hsm1]) (by simp [hsm1]) (by simp [hsm1]) hl200 hl192 hl136
    (Int.toBytes_length 8 _) hl160 hl184 hb0 ra rbp guard e0 e1 ity msg hm sp hity he0 hit RO MsgIn hmsg
    Heap (avail - 8 * n) (by omega)
    (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16)) ⋆ Eq ([4, 0, 0, 0].At rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 n).toInt).At (rax.toBitVec + 16))) R _
    (by simp) (by show (BitVec.ofNat 64 n).toNat = _; simp; omega)
    (by show (BitVec.ofNat 64 (4 * n)).toNat = _; simp; omega)
    (by simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega) hguard hsp
    (by
      dsimp only
      simp only [List.nil_append, Nat.sub_zero]
      rw [htl]
      ecancel) hno hlu hfe) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrsp2, hrbp2, Hm2⟩
  dsimp only at hpc2 hrax2 hrsp2 hrbp2 Hm2
  refine Eventually.done _ ⟨hpc2, hrax2, ?_, hrbp2, Hm2⟩
  apply UInt64.toBitVec_inj.mp; rw [hrsp2]; simp
