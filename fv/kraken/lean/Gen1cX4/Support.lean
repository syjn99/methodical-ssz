import Fk.Bytes
import Fk.Flags
import Fk.Contracts
import Fk.Frame

/-! Lemmas used by the proofs that fv/kraken/gen/x4 generates. Written by hand, not generated.
`ofBytes1` is the statement of `Fk.sc_ofBytes1` (Fk/ScRejectBool.lean), proved here again so the
generated modules do not import a hand proof module. -/

namespace Gen1cX4

theorem ofBytes1 (e : UInt8) : BitVec.ofInt 8 (Int.ofBytes [e]) = e.toBitVec := by
  have := e.toNat_lt
  apply BitVec.eq_of_toNat_eq
  simp [Int.ofBytes, BitVec.toNat_ofInt]

end Gen1cX4

namespace Gen1cX4

/-- The statement of `Fk.lu_off4` (Fk/LuReject.lean), proved here again: the 32-bit load of a
first offset, zero-extended and compared with 4. -/
theorem off4 (o4 : List UInt8) (ho4 : o4.length = 4)
    (h : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) - 4 = 0#64) : Int.ofBytes o4 = 4 := by
  have h0 := Int.ofBytes_ge_zero o4
  have h1 := Int.ofBytes_lt o4
  rw [ho4] at h1
  have hx : BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4)) = 4 := by
    rw [← BitVec.sub_add_cancel (BitVec.zeroExtend 64 (BitVec.ofInt 32 (Int.ofBytes o4))) 4, h]; rfl
  have := congrArg BitVec.toNat hx
  simp [BitVec.toNat_ofInt] at this
  omega

end Gen1cX4

namespace Gen1cX4
open Fk

/-! The statements of `staticBox_congr`, `and7_ne`, `and7_zero'`, `shr3_toNat'`, `jg16_true`,
`store_avx_step`, `lr_split16` and `join4` of Fk/LuRejectCall.lean (a hand proof module), proved
here again with the same text so the generated ListU64 call-path proofs (convT64 + fmt.errorf)
do not import a hand proof module. `and7_*`, `shr3_toNat'` and `jg16_true` are for 8-byte
elements and the limit 16: x4gen refuses other element sizes and limits on that path. -/

theorem staticBox_congr [Host] {x y : BitVec 64} (h : x = y) : StaticBox x = StaticBox y := h ▸ rfl

theorem and7_ne (x : BitVec 64) (h4 : 4 ≤ x.toNat) (h : (x.toNat - 4) % 8 ≠ 0) : (-4 + x) &&& 7 ≠ 0#64 := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [BitVec.toNat_and, BitVec.add_comm, ← BitVec.sub_eq_add_neg,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega),
    show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
  simp at this; omega

theorem and7_zero' (x : BitVec 64) (n : Nat) (h : x.toNat = 4 + 8 * n) : (-4 + x) &&& 7 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.add_comm, ← BitVec.sub_eq_add_neg,
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega),
    show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp; omega

theorem shr3_toNat' (x : BitVec 64) (n : Nat) (h : x.toNat = 4 + 8 * n) :
    (BitVec.ushiftRight (-4 + x) 3).toNat = n := by
  rw [show (-4 + x).ushiftRight 3 = (-4 + x) >>> 3 from rfl, BitVec.toNat_ushiftRight, BitVec.add_comm,
    ← BitVec.sub_eq_add_neg, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; simp; omega), Nat.shiftRight_eq_div_pow]
  simp; omega

/-- `cmp $16, a; jg` is taken when `16 < a < 2^62`. -/
theorem jg16_true (a : BitVec 64) (af : Bool) (h : 16 < a.toNat) (h2 : a.toNat < 2 ^ 62) :
    CondCode.g.interp (StatusFlags.from_result (a - 16)
      { cf := BitVec.unsigned (a - 16) != a.unsigned - BitVec.unsigned (16 : BitVec 64), af := af,
        of := BitVec.toInt (a - 16) != a.toInt - BitVec.toInt (16 : BitVec 64) }) = true := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have t16 : BitVec.toInt (16 : BitVec 64) = 16 := by decide
  have hs : (a - 16).toInt = (a.toNat : Int) - 16 := by
    rw [BitVec.toInt_sub, ta, t16]; apply Int.bmod_eq_of_le <;> omega
  have hz : a - 16 ≠ 0#64 := by
    intro h0; have := congrArg BitVec.toNat h0; simp [BitVec.toNat_sub] at this; omega
  have hm : (a - 16).msb = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_sub]; omega
  simp [CondCode.interp, StatusFlags.from_result, ta, t16, hs]
  refine ⟨by simpa using hz, ?_⟩
  rw [show (a - 16#64) = a - 16 from rfl, hm, Int.bmod_eq_of_le (by omega) (by omega)]; simp

/-- A 16-byte AVX store (`movups`) into a separated chunk. -/
theorem store_avx_step (s : MachineData) (addr : BitVec 64) {w : AvxWidth} (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (bs.At addr) ⋆ F) s.dmem) (hl : bs.length = w.bytes) (hw : w.bytes ≤ 2 ^ 64)
    (k : ∀ m', (Eq ((Int.toBytes w.bytes v.toInt).At addr) ⋆ F) m' → (ret { s with dmem := m' }).All post) :
    (MachineData.storeAvx s addr v ret).All post := by
  unfold MachineData.storeAvx
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [Effects.All_require_write_access]
  rw [Mem.loadInt_sep bs addr _ F s.dmem H hl hw]
  exact k _ (Mem.storeInt_sep addr w.bytes bs F s.dmem ⟨H, hl⟩ v.toInt)

theorem lr_split16 (bs : List UInt8) (h : bs.length = 16) (a : BitVec 64) :
    Eq (bs.At a) = Eq ((bs.take 8).At a) ⋆ Eq ((bs.drop 8).At (a + 8)) := by
  conv => lhs; rw [← List.take_append_drop 8 bs]
  rw [Mem.At_append_sep _ _ _ (by simp; omega)]; simp [h]

/-- Four 8-byte words as one argument array (two `any` values). -/
theorem join4 (a b c d : BitVec 64) (A0 A1 A2 A3 : List UInt8) (h0 : A0.length = 8) (h1 : A1.length = 8)
    (h2 : A2.length = 8) (h3 : A3.length = 8) (hb : b = a + 8) (hc : c = a + 16) (hd : d = a + 24) :
    Eq ((A0 ++ (A1 ++ (A2 ++ A3))).At a) = Eq (A0.At a) ⋆ Eq (A1.At b) ⋆ Eq (A2.At c) ⋆ Eq (A3.At d) := by
  rw [at_app A0 _ (b := b) (by rw [h0, hb]; rfl) (by simp [*]), at_app A1 _ (b := c) (by rw [h1, hb, hc]; bv_omega) (by simp [*]),
    at_app A2 A3 (b := d) (by rw [h2, hc, hd]; bv_omega) (by simp [*])]
  simp only [Std.ExtHashMap.sep_assoc]

end Gen1cX4

namespace Gen1cX4
open Fk

/-! The statements of `mix_split`, `mix_step`, `add8_neg8` (Fk/FvMarshal.lean) and `lum_addr`,
`lum_room`, `lum_rdx`, `inc_toNat16`, `idx8'`, `lum_off` (Fk/LuMarshal.lean), hand proof modules,
proved here again with the same text for the generated ListU64 marshal proof and its loop. -/

theorem mix_split (ws d : List UInt8) (i : Nat) :
    ws.take (8 * i) ++ d.drop (8 * i) = ws.take (8 * i) ++ ((d.drop (8 * i)).take 8 ++ d.drop (8 * i + 8)) := by
  rw [← List.drop_drop, List.take_append_drop]

theorem mix_step (ws d : List UInt8) (i : Nat) :
    ws.take (8 * i) ++ ((ws.drop (8 * i)).take 8 ++ d.drop (8 * i + 8)) = ws.take (8 * (i + 1)) ++ d.drop (8 * (i + 1)) := by
  rw [← List.append_assoc, ← List.take_add, show 8 * i + 8 = 8 * (i + 1) by omega]

theorem add8_neg8 (x y : BitVec 64) : 8 + y + x * 1#64 + -8 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 8, BitVec.add_assoc, BitVec.add_assoc]
  rw [show (-8 : BitVec 64) + 8 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

theorem lum_addr (x y : BitVec 64) (L i : Nat) (h : y.toNat = L + 4 + 8 * i) (hL : L + 4 + 8 * i < 2 ^ 63) :
    8 + y + x * 1#64 + -8 = x + BitVec.ofNat 64 (L + 4) + BitVec.ofNat 64 (8 * i) := by
  rw [add8_neg8, BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem lum_room (y z : BitVec 64) (L n i cap : Nat) (h : y.toNat = L + 4 + 8 * i) (hi : i < n)
    (hz : z.toNat = cap) (hc : L + 4 + 8 * n ≤ cap) (hc63 : cap < 2 ^ 63) : (8 + y).toNat ≤ z.toNat := by
  simp [BitVec.toNat_add]; omega

theorem lum_rdx (y : BitVec 64) (L i : Nat) (h : y.toNat = L + 4 + 8 * i) (hL : L + 4 + 8 * (i + 1) < 2 ^ 63) :
    (8 + y).toNat = L + 4 + 8 * (i + 1) := by
  simp [BitVec.toNat_add]; omega

theorem inc_toNat16 (x : BitVec 64) (i : Nat) (h : x.toNat = i) (hi : i < 16) : (x + 1).toNat = i + 1 := by
  simp [BitVec.toNat_add]; omega

theorem idx8' (x y : BitVec 64) (i : Nat) (h : y.toNat = i) (hi : i < 16) :
    x + y * 8#64 = x + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_mul]; omega

theorem lum_off (x y : BitVec 64) : y + 4 + x * 1#64 + -4 = x + y := by
  rw [BitVec.mul_one, BitVec.add_assoc, BitVec.add_assoc, BitVec.add_comm 4, BitVec.add_assoc,
    show (-4 : BitVec 64) + 4 = 0 by decide, Fk.add_lit_zero, BitVec.add_comm]

end Gen1cX4

namespace Gen1cX4
open Fk

/-! The definition `lcAcc` and the statements of `jl_val`, `sum_take_le`, `lcAcc_succ`, `lcAcc_le`
of Fk/LcSize.lean (a hand proof module), written here again with the same text so the generated
ListC size proof does not import a hand proof module. `lcAcc` is the sum after the first `i` items of
a list of single-list containers with 8-byte inner elements (offset 4 + inner fixed part 4 + 8·l):
x4gen refuses other element shapes on that path. -/

theorem jl_val (a b : BitVec 64) (ha : a.toNat < 2 ^ 62) (hb : b.toNat < 2 ^ 62) (af : Bool) :
    CondCode.l.interp (StatusFlags.from_result (a - b)
      { cf := BitVec.unsigned (a - b) != a.unsigned - b.unsigned, af := af,
        of := BitVec.toInt (a - b) != a.toInt - b.toInt }) = decide (a.toNat < b.toNat) := by
  have ta : a.toInt = a.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have tb : b.toInt = b.toNat := BitVec.toInt_eq_toNat_of_lt (by omega)
  have hs : (a - b).toInt = (a.toNat : Int) - b.toNat := by
    rw [BitVec.toInt_sub, ta, tb]; apply Int.bmod_eq_of_le <;> omega
  have hm : (a - b).msb = decide (a.toNat < b.toNat) := by
    rw [BitVec.msb_eq_toInt, hs]; simp; omega
  simp only [CondCode.interp, StatusFlags.from_result, hm, hs, ta, tb]
  simp
theorem sum_take_le (f : Nat → Nat) (ls : List Nat) (i : Nat) :
    ((ls.take i).map f).sum ≤ (ls.map f).sum := by
  conv => rhs; rw [← List.take_append_drop i ls]
  rw [List.map_append, List.sum_append]; omega

/-- The sum the loop computes after the first `i` elements. -/
def lcAcc (ls : List Nat) (i : Nat) : Nat := 4 + ((ls.take i).map fun l => 8 + 8 * l).sum

theorem lcAcc_succ (ls : List Nat) (i : Nat) (hi : i < ls.length) :
    lcAcc ls (i + 1) = lcAcc ls i + 8 + 8 * ls[i] := by
  simp only [lcAcc, List.take_add_one, List.map_append, List.sum_append, List.getElem?_eq_getElem hi]
  simp; omega

theorem lcAcc_le (ls : List Nat) (i : Nat) : lcAcc ls i ≤ lcAcc ls ls.length := by
  simp only [lcAcc, List.take_length]
  have := sum_take_le (fun l => 8 + 8 * l) ls i
  omega

end Gen1cX4
