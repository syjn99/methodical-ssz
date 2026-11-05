import Fk.Step
import Fk.Labels
import Fk.Flags
import Fk.Vbv
import Fk.Bump
import Fv1.SpecBitList

/-!
# `ssz.ValidateBitlist`: contract, EthLib rule, and a model (re-proof R4)

Go's `ssz.ValidateBitlist` uses `bsr` (`bits.Len8`), which Kraken does not
parse, so `ValidateBitlistC` stays a hypothesis of the BitL theorems (the
decoder since 1b, the encoder since the generator fix F2).

`blValid_iff`: with the limit 2048, EthLib's `unpackDelimited` accepts n bytes
exactly when `1 ≤ n ≤ 257`, the last byte is non-zero, and for n = 257 the
last byte is 1 (`blArith`).

`RtVbl` (Fk/RtVbl.S) computes `blArith` without `bsr`. On an invalid input it
takes 16 zero bytes from the bump heap (an `*errors.errorString` with the
empty message) and returns the errorString itab in rax and the object in rbx.
`rt_validate_bitlist` and `rt_validate_bitlist_err` prove that this code meets
`ValidateBitlistC S` and `ValidateBitlistErrC bumpHeap S` for every `S`. This
shows that the contracts are satisfiable together and gives a host for the
BitL witnesses; it is not a proof about Go's code.
-/

open Fk Fv1 EthLib.Serialization.Ssz

namespace Fk
def RtVbl : Program := include_x64_rt "Fk/RtVbl.S"
end Fk

variable [Host]

/-- The bitlist rule (EthLib): `unpackDelimited` with the limit 2048 accepts. -/
def blValid (tl : List UInt8) : Prop := ∃ bits, unpackDelimited (some 2048) tl.toArray = .ok bits

/-- `ssz.ValidateBitlist(buf []byte, bitLimit uint64) error` (rax = ptr,
rbx = len, rcx = cap, rdi = limit), valid input (re-proof fix X5: split by
the input). If `blValid buf`, it returns to the return address with rsp + 8,
r14 and rbp kept, rax = 0 (nil error), the frame `F` and the bytes unchanged.
It allocates nothing on this path. The 32-byte spill area of its four
register arguments is the callee's. -/
def ValidateBitlistC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (buf stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = buf.length → st.regs.rdi = 2048 → stk.length = S → spill.length = 32 → blValid buf →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.rax = 0 ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 32 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "ssz.ValidateBitlist"⟩

/-- `ssz.ValidateBitlist`, invalid input (re-proof fix X5). If `¬ blValid buf`
and the heap has the budget (`8192 ≤ avail`), it returns a non-nil error:
rax is the `*errors.errorString` itab, rbx is the data pointer `e`, and the
error object `ErrStr e sp msg` (16 bytes and the message, at most 128 bytes)
comes from the heap: `avail' + 16 + msg.length ≤ avail ≤ avail' + 8192`.
Every error of Go 1.26.3 `ValidateBitlist` is `fmt.Errorf` without `%w`, so
`errors.New(s)` (trusted, CONTRACTS.md 1d: Go's constant messages are in
rodata, not the heap; the longest message has 81 bytes). -/
def ValidateBitlistErrC (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (buf stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = buf.length → st.regs.rdi = 2048 → stk.length = S → spill.length = 32 → ¬ blValid buf →
    8192 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.rax.toBitVec = (label "go_itab._errors.errorString_error").toBitVec ∧
        ∃ (stk' spill' msg : List UInt8) (sp : BitVec 64) (avail' : Nat), stk'.length = S ∧ spill'.length = 32
          ∧ msg.length ≤ 128 ∧ avail' + 16 + msg.length ≤ avail ∧ avail ≤ avail' + 8192 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ ErrStr st'.data.regs.rbx.toBitVec sp msg ⋆ Heap avail' ⋆ F)
          st'.data.dmem)
      ⟨st, label "ssz.ValidateBitlist"⟩


set_option maxRecDepth 100000 in
theorem highestBit_fin : ∀ b : Fin 256,
    highestBit (UInt8.ofNat b) ≤ 7 ∧ (highestBit (UInt8.ofNat b) = 0 ↔ b.val ≤ 1) := by decide

theorem highestBit_prop (b : UInt8) : highestBit b ≤ 7 ∧ (highestBit b = 0 ↔ b.toNat ≤ 1) := by
  have := highestBit_fin ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-- The bitlist rule with the limit 2048, as arithmetic on the length and the last byte. -/
def blArith (tl : List UInt8) : Prop :=
  tl ≠ [] ∧ tl.length ≤ 257 ∧ tl.getLastD 0 ≠ 0 ∧ (tl.length = 257 → tl.getLastD 0 = 1)

theorem blValid_iff (tl : List UInt8) :
    (∃ bits, unpackDelimited (some 2048) tl.toArray = .ok bits) ↔ blArith tl := by
  unfold unpackDelimited blArith
  simp only [List.size_toArray, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  have hl : ∀ (tl : List UInt8), tl ≠ [] → tl.toArray[tl.length - 1]! = tl.getLastD 0 := by
    intro tl h
    obtain ⟨xs, x, rfl⟩ := List.eq_nil_or_concat tl |>.resolve_left h
    simp [getElem!_def]
  by_cases h0 : tl = []
  · subst h0; simp
  rw [hl tl h0]
  generalize tl.getLastD 0 = b
  have hb := highestBit_prop b
  have hn : tl.length ≠ 0 := by simpa using h0
  simp only [beq_iff_eq, hn, ↓reduceIte, ne_eq, h0, not_false_eq_true, true_and]
  by_cases hz : b = 0
  · simp only [hz, ↓reduceIte]; split <;> simp
  · simp only [hz, ↓reduceIte, not_false_eq_true, true_and]
    have : b.toNat ≠ 0 := fun e => hz (UInt8.toNat_inj.mp (by simpa using e))
    obtain ⟨hb7, hb0⟩ := hb
    split
    · simp only [reduceCtorEq, exists_const, false_iff, not_and, Classical.not_imp]
      intro h
      refine ⟨by omega, fun e => ?_⟩
      subst e; have := hb0.mpr (by decide); omega
    · simp only [Except.ok.injEq, exists_eq', true_iff]
      refine ⟨by omega, fun e => ?_⟩
      have h1 : highestBit b = 0 := by omega
      have := hb0.mp h1
      apply UInt8.toNat_inj.mp; simp; omega

open Fk Fk.Code

namespace Fk

theorem cmp_a_iff (a b : BitVec 64) (af of' : Bool) :
    CondCode.a.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af, of := of' }) = decide (b.toNat < a.toNat) := by
  by_cases h : b.toNat ≤ a.toNat
  · have hs : (a - b).toNat = a.toNat - b.toNat := BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    by_cases he : b.toNat = a.toNat
    · have : a - b = 0#64 := by apply BitVec.eq_of_toNat_eq; rw [hs]; simp; omega
      simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, this, hs]; omega
    · have hz : a - b ≠ 0#64 := by intro h0; have := congrArg BitVec.toNat h0; rw [hs] at this; simp at this; omega
      simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hs]
      have hz' : (a - b == BitVec.zero 64) = false := by simpa [BitVec.zero] using hz
      rw [hz']
      have : (((a.toNat - b.toNat : Nat) : Int) != (a.toNat : Int) - (b.toNat : Int)) = false := by
        simp only [bne_eq_false_iff_eq]; omega
      rw [this]; simp; omega
  · have hb : (a - b).toNat = 2 ^ 64 - b.toNat + a.toNat := by rw [BitVec.toNat_sub]; have := b.isLt; omega
    simp only [CondCode.interp, StatusFlags.from_result, BitVec.unsigned, hb]
    have : (((2 ^ 64 - b.toNat + a.toNat : Nat) : Int) != (a.toNat : Int) - (b.toNat : Int)) = true := by
      simp only [bne_iff_ne, ne_eq]; have := b.isLt; omega
    rw [this]; simp; omega

theorem cmp_nz_iff (a b : BitVec 64) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = decide (a ≠ b) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.zero]
  by_cases h : a = b
  · subst h; simp
  · have : (a - b == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [this, h]

theorem vbl_ecx (b : UInt8) :
    BitVec.extractLsb' 0 32 (BitVec.zeroExtend 64 (BitVec.zeroExtend 32 (BitVec.ofInt 8 (Int.ofBytes [b]))))
      = BitVec.ofNat 32 b.toNat := by
  apply BitVec.eq_of_toNat_eq; simp [Int.ofBytes, BitVec.toNat_ofInt]

theorem vbl_z (b : UInt8) : (BitVec.ofNat 32 b.toNat == 0) = (b == 0) := by
  by_cases h : b = 0
  · subst h; rfl
  · have : (b == 0) = false := by simpa using h
    rw [this]; simp only [beq_eq_false_iff_ne, ne_eq]; intro h'; apply h
    apply UInt8.toNat_inj.mp; have := congrArg BitVec.toNat h'; simp at this; simp; omega

theorem cmp_nz_iff32 (a b : BitVec 32) (f : StatusFlags.from_result.Remaining) :
    CondCode.nz.interp (StatusFlags.from_result (a - b) f) = decide (a ≠ b) := by
  simp only [CondCode.interp, StatusFlags.from_result, BitVec.zero]
  by_cases h : a = b
  · subst h; simp
  · have : (a - b == 0#32) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [this, h]

theorem vbl_one (b : UInt8) : (BitVec.ofNat 32 b.toNat ≠ (1 : BitVec 32)) ↔ b ≠ 1 := by
  constructor
  · intro h e; apply h; subst e; rfl
  · intro h e; apply h; apply UInt8.toNat_inj.mp; have := congrArg BitVec.toNat e; simp at this; simp; omega

theorem blArith_cons_len (init : List UInt8) (last : UInt8) :
    blArith (init ++ [last]) ↔ init.length + 1 ≤ 257 ∧ last ≠ 0 ∧ (init.length + 1 = 257 → last = 1) := by
  simp [blArith]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `RtVbl` meets the valid-input contract (re-proof fix X5). The error
branches contradict `blValid`. -/
theorem rt_validate_bitlist (j : Nat) (hj : RtVbl.IsInfixAt Host.prog j) (hf : LabelsFresh RtVbl j) (S : Nat) :
    ValidateBitlistC S := by
  intro st ret buf stk spill F hrbx hrdi hstk hsp hval hm
  have ha := (blValid_iff buf).mp hval
  rw [label_at' hj hf (j := 0) (l := "ssz.ValidateBitlist") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrbx hrdi hm ⊢
  kat hj RtVbl 0
  kat hj RtVbl 1
  intro _
  kat hj RtVbl 2
  rw [vbv_zand]
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat buf |>.resolve_left ha.1
  rw [List.concat_eq_append] at hm hrbx ha ⊢
  rw [blArith_cons_len] at ha
  obtain ⟨hlen, hz, h1⟩ := ha
  simp only [List.length_append, List.length_singleton] at hrbx
  have hne : (rbx.toBitVec == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 3
  kat hj RtVbl 4
  rw [cmp_a_iff]
  have : decide ((257 : BitVec 64).toNat < rbx.toBitVec.toNat) = false := by simp; omega
  rw [this]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 5
  rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))] at hm
  rw [vbv_last_addr _ _ _ (by simpa using hrbx.symm)]
  apply load_step _ _ _ _ [last] _ _ (by ecancel) (by rfl)
  kunfold
  kat hj RtVbl 6
  intro _
  kat hj RtVbl 7
  rw [vbl_ecx, vbv_zand, vbl_z]
  simp only [show (last == 0) = false by simpa using hz, Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 8
  kat hj RtVbl 9
  rw [cmp_nz_iff]
  by_cases h257 : init.length + 1 = 257
  · have : decide (rbx.toBitVec ≠ 257) = false := by
      simp only [decide_eq_false_iff_not]; intro h; apply h; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hj RtVbl 10
    kat hj RtVbl 11
    rw [vbl_ecx, cmp_nz_iff32]
    have hl1 := h1 h257
    simp only [show decide (BitVec.ofNat 32 last.toNat ≠ BitVec.truncate 32 (1 : BitVec 64)) = false by rw [hl1]; decide,
      Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hj RtVbl 12
    kat hj RtVbl 13
    intro _
    kat hj RtVbl 14
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, stk, spill, hstk, hsp,
      by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
    apply UInt64.toBitVec_inj.mp; simp
  · have : decide (rbx.toBitVec ≠ 257) = true := by
      simp only [decide_eq_true_iff]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
    rw [this]
    simp only [↓reduceIte, Effects.All]
    klabel hj hf RtVbl 12
    kat hj RtVbl 12
    kat hj RtVbl 13
    intro _
    kat hj RtVbl 14
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, stk, spill, hstk, hsp,
      by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
    apply UInt64.toBitVec_inj.mp; simp

theorem rtvbl_heap_split (avail : Nat) (h : 8192 ≤ avail) :
    List.replicate avail (0 : UInt8) = List.replicate 16 0 ++ List.replicate (avail - 16) 0 := by
  rw [List.replicate_append_replicate]; congr 1; omega

theorem vbl_nil_At_emp (a : BitVec 64) : Eq (([] : List UInt8).At a) = Std.ExtHashMap.emp := by
  funext m; apply propext; simp only [List.At, List.mapIdx_nil, Std.ExtHashMap.ofList_nil, Std.ExtHashMap.emp]
  exact ⟨Eq.symm, Eq.symm⟩

theorem rtvbl_16 (p : BitVec 64) : p + BitVec.ofNat 64 16 = p + (16 : BitVec 64) := rfl

theorem rtvbl_obj0 : Int.toBytes 8 (0 : BitVec 64).toInt ++ Int.toBytes 8 (BitVec.ofNat 64 0).toInt
    = List.replicate 16 (0 : UInt8) := by rfl

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `RtVbl` meets the invalid-input contract with the bump heap (re-proof fix
X5): every error branch takes 16 zero bytes (an errorString with the empty
message) from the heap; the valid branches contradict `¬ blValid`. -/
theorem rt_validate_bitlist_err (j : Nat) (hj : RtVbl.IsInfixAt Host.prog j) (hf : LabelsFresh RtVbl j) (S : Nat) :
    ValidateBitlistErrC bumpHeap S := by
  intro st ret avail buf stk spill F hrbx hrdi hstk hsp hinv hav hm
  rw [blValid, blValid_iff] at hinv
  rw [label_at' hj hf (j := 0) (l := "ssz.ValidateBitlist") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrbx hrdi hm ⊢
  have hm' : (bumpHeap avail ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (rsp.toBitVec + 8))
      ⋆ Eq (buf.At rax.toBitVec) ⋆ F)) mem := by ecancel
  obtain ⟨p, hp⟩ := sep_exists_left (Q := fun (p : BitVec 64) (m : DataMem) => p.toNat + avail < 2 ^ 64 ∧
    (Eq ((Int.toBytes 8 p.toInt).At (label "runtime.fvBump").toBitVec) ⋆ Eq ((List.replicate avail 0).At p)) m) hm'
  obtain ⟨hpa, hp⟩ := sep_pure_left hp
  clear hm hm'
  kat hj RtVbl 0
  kat hj RtVbl 1
  intro _
  kat hj RtVbl 2
  rw [vbv_zand]
  by_cases hn : buf = []
  · subst hn
    have he : (rbx.toBitVec == 0) = true := by
      simp only [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simpa using hrbx
    rw [he]
    simp only [↓reduceIte, Effects.All]
    klabel hj hf RtVbl 15
    kat hj RtVbl 15
    kat hj RtVbl 16
    apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hj RtVbl 17
    kat hj RtVbl 18
    apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m1 H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    kat hj RtVbl 19
    kat hj RtVbl 20
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    rw [rtvbl_heap_split avail hav, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
    simp only [List.length_replicate, rtvbl_16, Std.ExtHashMap.sep_emp] at H1
    have hq : (p + (16 : BitVec 64)).toNat = p.toNat + 16 := by
      simp only [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl]; omega
    have H2 : ((Eq ((Int.toBytes 8 (p + (16 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
        ⋆ Eq ((List.replicate (avail - 16) 0).At (p + (16 : BitVec 64))))
        ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq (([] : List UInt8).At rax.toBitVec) ⋆ Eq ((List.replicate 16 0).At p) ⋆ F)) m1 := by
      ecancel
    have H3 := sep_mono_left (P' := bumpHeap (avail - 16)) (fun m hm => ⟨p + (16 : BitVec 64), by omega, hm⟩) H2
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, by simp, stk, spill, [], 0, avail - 16,
      hstk, hsp, by simp, by simp; omega, by omega, ?_⟩
    simp only [ErrStr, List.length_nil, rtvbl_obj0, vbl_nil_At_emp, Std.ExtHashMap.sep_emp,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at H3 ⊢
    ecancel
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat buf |>.resolve_left hn
  rw [List.concat_eq_append] at hp hrbx hinv ⊢
  rw [blArith_cons_len] at hinv
  simp only [List.length_append, List.length_singleton] at hrbx
  have hne : (rbx.toBitVec == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rw [hne]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 3
  kat hj RtVbl 4
  rw [cmp_a_iff]
  by_cases hbig : 257 < init.length + 1
  · have : decide ((257 : BitVec 64).toNat < rbx.toBitVec.toNat) = true := by simp; omega
    rw [this]
    simp only [↓reduceIte, Effects.All]
    klabel hj hf RtVbl 15
    kat hj RtVbl 15
    kat hj RtVbl 16
    apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hj RtVbl 17
    kat hj RtVbl 18
    apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m1 H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    kat hj RtVbl 19
    kat hj RtVbl 20
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    rw [rtvbl_heap_split avail hav, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
    simp only [List.length_replicate, rtvbl_16, Std.ExtHashMap.sep_emp] at H1
    have hq : (p + (16 : BitVec 64)).toNat = p.toNat + 16 := by
      simp only [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl]; omega
    have H2 : ((Eq ((Int.toBytes 8 (p + (16 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
        ⋆ Eq ((List.replicate (avail - 16) 0).At (p + (16 : BitVec 64))))
        ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((init ++ [last]).At rax.toBitVec) ⋆ Eq ((List.replicate 16 0).At p) ⋆ F)) m1 := by
      ecancel
    have H3 := sep_mono_left (P' := bumpHeap (avail - 16)) (fun m hm => ⟨p + (16 : BitVec 64), by omega, hm⟩) H2
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, by simp, stk, spill, [], 0, avail - 16,
      hstk, hsp, by simp, by simp; omega, by omega, ?_⟩
    simp only [ErrStr, List.length_nil, rtvbl_obj0, vbl_nil_At_emp, Std.ExtHashMap.sep_emp,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at H3 ⊢
    ecancel
  have : decide ((257 : BitVec 64).toNat < rbx.toBitVec.toNat) = false := by simp; omega
  rw [this]
  simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 5
  rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))] at hp
  rw [vbv_last_addr _ _ _ (by simpa using hrbx.symm)]
  apply load_step _ _ _ _ [last] _ _ (by ecancel) (by rfl)
  kunfold
  kat hj RtVbl 6
  intro _
  kat hj RtVbl 7
  rw [vbl_ecx, vbv_zand, vbl_z]
  by_cases hz : last = 0
  · simp only [show (last == 0) = true by simpa using hz, ↓reduceIte, Effects.All]
    rw [← Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))] at hp
    klabel hj hf RtVbl 15
    kat hj RtVbl 15
    kat hj RtVbl 16
    apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hj RtVbl 17
    kat hj RtVbl 18
    apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m1 H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    kat hj RtVbl 19
    kat hj RtVbl 20
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    rw [rtvbl_heap_split avail hav, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
    simp only [List.length_replicate, rtvbl_16, Std.ExtHashMap.sep_emp] at H1
    have hq : (p + (16 : BitVec 64)).toNat = p.toNat + 16 := by
      simp only [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl]; omega
    have H2 : ((Eq ((Int.toBytes 8 (p + (16 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
        ⋆ Eq ((List.replicate (avail - 16) 0).At (p + (16 : BitVec 64))))
        ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((init ++ [last]).At rax.toBitVec) ⋆ Eq ((List.replicate 16 0).At p) ⋆ F)) m1 := by
      ecancel
    have H3 := sep_mono_left (P' := bumpHeap (avail - 16)) (fun m hm => ⟨p + (16 : BitVec 64), by omega, hm⟩) H2
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, by simp, stk, spill, [], 0, avail - 16,
      hstk, hsp, by simp, by simp; omega, by omega, ?_⟩
    simp only [ErrStr, List.length_nil, rtvbl_obj0, vbl_nil_At_emp, Std.ExtHashMap.sep_emp,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at H3 ⊢
    ecancel
  simp only [show (last == 0) = false by simpa using hz, Bool.false_eq_true, ↓reduceIte, Effects.All]
  kat hj RtVbl 8
  kat hj RtVbl 9
  rw [cmp_nz_iff]
  by_cases h257 : init.length + 1 = 257
  · have : decide (rbx.toBitVec ≠ 257) = false := by
      simp only [decide_eq_false_iff_not]; intro h; apply h; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [this]
    simp only [Bool.false_eq_true, ↓reduceIte, Effects.All]
    kat hj RtVbl 10
    kat hj RtVbl 11
    rw [vbl_ecx, cmp_nz_iff32]
    by_cases h1 : last = 1
    · exfalso; exact hinv ⟨by omega, hz, fun _ => h1⟩
    simp only [show decide (BitVec.ofNat 32 last.toNat ≠ BitVec.truncate 32 (1 : BitVec 64)) = true by
        simpa using (vbl_one last).mpr h1,
      ↓reduceIte, Effects.All]
    rw [← Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))] at hp
    klabel hj hf RtVbl 15
    kat hj RtVbl 15
    kat hj RtVbl 16
    apply load_step _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    kat hj RtVbl 17
    kat hj RtVbl 18
    apply store_step _ _ _ _ _ (Int.toBytes 8 p.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m1 H1
    simp only [Width.bytes, Width.bits] at H1
    kunfold
    kat hj RtVbl 19
    kat hj RtVbl 20
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    rw [rtvbl_heap_split avail hav, Mem.At_append_sep _ _ _ (by simp; omega)] at H1
    simp only [List.length_replicate, rtvbl_16, Std.ExtHashMap.sep_emp] at H1
    have hq : (p + (16 : BitVec 64)).toNat = p.toNat + 16 := by
      simp only [BitVec.toNat_add, show (16 : BitVec 64).toNat = 16 from rfl]; omega
    have H2 : ((Eq ((Int.toBytes 8 (p + (16 : BitVec 64)).toInt).At (label "runtime.fvBump").toBitVec)
        ⋆ Eq ((List.replicate (avail - 16) 0).At (p + (16 : BitVec 64))))
        ⋆ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At rsp.toBitVec) ⋆ Eq (stk.At (rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (spill.At (rsp.toBitVec + 8)) ⋆ Eq ((init ++ [last]).At rax.toBitVec) ⋆ Eq ((List.replicate 16 0).At p) ⋆ F)) m1 := by
      ecancel
    have H3 := sep_mono_left (P' := bumpHeap (avail - 16)) (fun m hm => ⟨p + (16 : BitVec 64), by omega, hm⟩) H2
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, by simp, stk, spill, [], 0, avail - 16,
      hstk, hsp, by simp, by simp; omega, by omega, ?_⟩
    simp only [ErrStr, List.length_nil, rtvbl_obj0, vbl_nil_At_emp, Std.ExtHashMap.sep_emp,
      BitVec.ofInt_ofBytes_toBytes 64 8 rfl, Fk.ofInt_ofBytes_toBytes64] at H3 ⊢
    ecancel
  · exfalso; exact hinv ⟨by omega, hz, fun e => absurd e h257⟩
