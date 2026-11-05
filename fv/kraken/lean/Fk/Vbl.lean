import Fk.Step
import Fk.Labels
import Fk.Flags
import Fk.Vbv
import Fv1.SpecBitList

/-!
# `ssz.ValidateBitlist`: contract, EthLib rule, and a model (re-proof R4)

Go's `ssz.ValidateBitlist` uses `bsr` (`bits.Len8`), which Kraken does not
parse, so `ValidateBitlistC` stays a hypothesis of the BitL theorems (the
decoder since 1b, the encoder since the generator fix F2).

`blValid_iff`: with the limit 2048, EthLib's `unpackDelimited` accepts n bytes
exactly when `1 ≤ n ≤ 257`, the last byte is non-zero, and for n = 257 the
last byte is 1 (`blArith`).

`RtVbl` (Fk/RtVbl.S) computes `blArith` without `bsr` and returns rax = 1 on
an invalid input. `rt_validate_bitlist` proves that this code meets
`ValidateBitlistC S` for every `S`. This shows that the contract is
satisfiable and gives a host for the BitL witnesses; it is not a proof about
Go's code.
-/

open Fk Fv1 EthLib.Serialization.Ssz

namespace Fk
def RtVbl : Program := include_x64_rt "Fk/RtVbl.S"
end Fk

variable [Host]

/-- The bitlist rule (EthLib): `unpackDelimited` with the limit 2048 accepts. -/
def blValid (tl : List UInt8) : Prop := ∃ bits, unpackDelimited (some 2048) tl.toArray = .ok bits

/-- `ssz.ValidateBitlist(buf []byte, bitLimit uint64) error` (rax = ptr,
rbx = len, rcx = cap, rdi = limit): returns to the return address with
rsp + 8, r14 and rbp kept, the frame `F` and the bytes unchanged, and rax = 0
(nil error) exactly when `blValid` holds. The 32-byte spill area of its four
register arguments is the callee's. The error's second word (rbx) is not
specified. On an invalid input rax is the `*errors.errorString` itab: every
error of Go 1.26.3 `ValidateBitlist` comes from `fmt.Errorf` without `%w`,
which returns `errors.New(s)` (trusted, CONTRACTS.md). -/
def ValidateBitlistC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (buf stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = buf.length → st.regs.rdi = 2048 → stk.length = S → spill.length = 32 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp ∧ (st'.data.regs.rax = 0 ↔ blValid buf)
        ∧ (¬ blValid buf → st'.data.regs.rax.toBitVec = (label "go_itab._errors.errorString_error").toBitVec) ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 32 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (buf.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
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

/-- The error tail of `RtVbl` (from `L_fvbl_err`): rax = 1. -/
theorem rtvbl_err_ne : ¬ ((1 : UInt64) = 0) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem rt_validate_bitlist (j : Nat) (hj : RtVbl.IsInfixAt Host.prog j) (hf : LabelsFresh RtVbl j) (S : Nat)
    (hit : (label "go_itab._errors.errorString_error").toBitVec ≠ 0) :
    ValidateBitlistC S := by
  intro st ret buf stk spill F hrbx hrdi hstk hsp hm
  rw [label_at' hj hf (j := 0) (l := "ssz.ValidateBitlist") (by rfl) (by rfl)]
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := st
  simp only at hrbx hrdi hm ⊢
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
    kat hj RtVbl 17
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, fun _ => rfl, stk, spill, hstk, hsp,
      by ecancel⟩
    rw [blValid, blValid_iff]
    constructor
    · intro h; dsimp only at h; exact absurd (congrArg UInt64.toBitVec h) hit
    · intro h'
      exfalso
      exact h'.1 rfl
  obtain ⟨init, last, rfl⟩ := List.eq_nil_or_concat buf |>.resolve_left hn
  rw [List.concat_eq_append] at hm hrbx ⊢
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
    kat hj RtVbl 17
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, fun _ => rfl, stk, spill, hstk, hsp,
      by ecancel⟩
    rw [blValid, blValid_iff]
    constructor
    · intro h; dsimp only at h; exact absurd (congrArg UInt64.toBitVec h) hit
    · intro h'
      exfalso
      exact absurd ((blArith_cons_len init last).mp h').1 (by omega)
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
  by_cases hz : last = 0
  · simp only [show (last == 0) = true by simpa using hz, ↓reduceIte, Effects.All]
    klabel hj hf RtVbl 15
    kat hj RtVbl 15
    kat hj RtVbl 16
    kat hj RtVbl 17
    apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
    kunfold
    apply Eventually.done
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, fun _ => rfl, stk, spill, hstk, hsp,
      by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
    rw [blValid, blValid_iff, blArith_cons_len]
    constructor
    · intro h; dsimp only at h; exact absurd (congrArg UInt64.toBitVec h) hit
    · intro h'
      exfalso
      exact h'.2.1 hz
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
    · simp only [show decide (BitVec.ofNat 32 last.toNat ≠ BitVec.truncate 32 (1 : BitVec 64)) = false by rw [h1]; decide,
        Bool.false_eq_true, ↓reduceIte, Effects.All]
      kat hj RtVbl 12
      kat hj RtVbl 13
      intro _
      kat hj RtVbl 14
      apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
      kunfold
      apply Eventually.done
      refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, ?nv, stk, spill, hstk, hsp,
        by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
      case nv => intro h; exfalso; apply h; rw [blValid, blValid_iff, blArith_cons_len]; exact ⟨by omega, by rw [h1]; decide, fun _ => h1⟩
      rw [blValid, blValid_iff, blArith_cons_len]
      refine ⟨fun _ => ⟨by omega, ?_, ?_⟩, fun _ => ?_⟩
      · rw [h1]; decide
      · intro _; exact h1
      · dsimp only; apply UInt64.toBitVec_inj.mp; simp
    · simp only [show decide (BitVec.ofNat 32 last.toNat ≠ BitVec.truncate 32 (1 : BitVec 64)) = true by
          simpa using (vbl_one last).mpr h1,
        ↓reduceIte, Effects.All]
      klabel hj hf RtVbl 15
      kat hj RtVbl 15
      kat hj RtVbl 16
      kat hj RtVbl 17
      apply load_step _ _ _ _ (Int.toBytes 8 ret.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
      kunfold
      apply Eventually.done
      refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, fun _ => rfl, stk, spill, hstk, hsp,
        by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
      rw [blValid, blValid_iff, blArith_cons_len]
      constructor
      · intro h; dsimp only at h; exact absurd (congrArg UInt64.toBitVec h) hit
      · intro h'
        exfalso
        exact h1 (h'.2.2 h257)
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
    refine ⟨by simp [BitVec.ofInt_ofBytes_toBytes 64 8 rfl], rfl, rfl, rfl, ?_, ?nv, stk, spill, hstk, hsp,
      by rw [Mem.At_append_sep _ _ _ (vbv_split init last rbx.toBitVec (by simpa using hrbx.symm))]; ecancel⟩
    case nv => intro h; exfalso; apply h; rw [blValid, blValid_iff, blArith_cons_len]; exact ⟨by omega, hz, fun e => absurd e h257⟩
    rw [blValid, blValid_iff, blArith_cons_len]
    refine ⟨fun _ => ⟨by omega, ?_, ?_⟩, fun _ => ?_⟩
    · exact hz
    · intro h; exact absurd h h257
    · dsimp only; apply UInt64.toBitVec_inj.mp; simp
