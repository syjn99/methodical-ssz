import Kraken.X64.WP
import Kraken.X64.Sep
import Kraken.Tactics
import Kraken.SeparationTactics
import Fk.Code
import Std.Tactic.BVDecide

/-! Our glue on top of Kraken main (6064eec): one-directive steps inside a `Host`. -/

open Fk.Code

namespace Fk

/-- Kraken computes `disp(%reg)` as `BitVec.ofInt 64 (reg.toInt + disp)`. -/
theorem ofInt_toInt_add (x : BitVec 64) (c : Int) :
    BitVec.ofInt 64 (x.toInt + c) = x + BitVec.ofInt 64 c := by
  rw [BitVec.ofInt_add, BitVec.ofInt_toInt]

/-- `sym(%rip)`: Kraken computes `ofInt (next.toInt + (sym - next).toInt)`. -/
theorem rip_addr (u l : Int64) : BitVec.ofInt 64 (u.toInt + (l - u).toInt) = l.toBitVec := by
  rw [BitVec.ofInt_add, Int64.toInt, Int64.toInt, BitVec.ofInt_toInt, BitVec.ofInt_toInt,
    Int64.toBitVec_sub]
  bv_omega

/-- `rip_addr` after simp has expanded `Int64` subtraction into `bmod`. -/
theorem rip_addr' (u l : Int64) :
    u.toBitVec + BitVec.ofInt 64 ((l.toInt - u.toInt).bmod 18446744073709551616) = l.toBitVec := by
  have := rip_addr u l
  rw [BitVec.ofInt_add, Int64.toInt, BitVec.ofInt_toInt] at this
  rw [← this, Int64.toInt_sub]

theorem ofInt_int64 (x : Int64) : BitVec.ofInt 64 x.toInt = x.toBitVec := by
  rw [Int64.toInt, BitVec.ofInt_toInt]

-- The normalization set Kraken's Examples.lean registers (file-local there), plus ours.
attribute [ksimp]
  BitVec.add_zero BitVec.ofInt_add BitVec.ofInt_ofNat BitVec.ofInt_toInt BitVec.ofNat_uInt64ToNat
  BitVec.setWidth_eq Int.add_zero Int64.toInt_neg Nat.shiftRight_zero Nat.sub_zero
  UInt64.ofBitVec_add UInt64.ofBitVec_ofNat UInt64.ofBitVec_sub UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel UInt64.toBitVec_ofNat UInt64.toBitVec_sub UInt64.toNat_toBitVec
  BitVec.ofNat_toNat rip_addr rip_addr' ofInt_int64

theorem isInfixAt_drop {α : Type} {p l : List α} {k : Nat} (h : p.IsInfixAt l k) (j : Nat) :
    (p.drop j).IsInfixAt l (k + j) := by
  rw [List.isInfixAt_iff_getElem?] at *
  intro i hi
  simp only [List.length_drop] at hi
  have := h (j + i) (by omega)
  rw [Nat.add_assoc, this, List.getElem_drop]

variable [Host]

/-- One directive of a fragment at index `k`, chained into `Eventually`. -/
theorem estep {k : Nat} {d : Directive} {p : Program} (hdp : (d :: p).IsInfixAt Host.prog k)
    {final : MachineState → Prop} {s : MachineData}
    (h : (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All
        (Eventually (step1 Host.exe) final)) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf k⟩ :=
  eventually_trans _ _ _ _ (Host.eventually_of_interp hdp h) (fun _ h => h)

end Fk
