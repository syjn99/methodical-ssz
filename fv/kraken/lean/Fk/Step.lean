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

theorem extractLsb'_full {w : Nat} (x : BitVec w) : x.extractLsb' 0 w = x := by
  ext i; simp

theorem add_ofNat_zero {w : Nat} (x : BitVec w) : x + BitVec.ofNat w 0 = x := by simp
theorem add_ofInt_zero {w : Nat} (x : BitVec w) : x + BitVec.ofInt w 0 = x := by simp
/-- `jmp sym`: Kraken computes the target as `next + (sym - next)`. -/
theorem jmp_rel (u l : Int64) : Int64.ofBitVec ((u + (l - u)).toBitVec) = l := by
  have : u + (l - u) = l := by rw [Int64.add_comm, Int64.sub_add_cancel]
  rw [this]; rfl

theorem add_lit_zero {w : Nat} (x : BitVec w) : x + (0 : BitVec w) = x := by simp
theorem add_int64_zero (x : BitVec 64) : x + Int64.toBitVec 0 = x := by
  rw [show Int64.toBitVec 0 = 0#64 from rfl]; simp

/-- A load from a separated chunk, without `kstep`'s `grind`. -/
theorem load_step (s : MachineData) (addr : BitVec 64) (w : Width) (ret : w.type → MachineData → Effects)
    (bs : List UInt8) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (bs.At addr) ⋆ F) s.dmem) (hl : bs.length = w.bytes)
    (k : (ret (.ofInt w.bits (Int.ofBytes bs)) s).All post) :
    (MachineData.load s addr w ret).All post := by
  rw [load_sep s addr w ret bs F H hl, Effects.All_require_read_access]; exact k

/-- A store into a separated chunk; the new memory is a fresh variable. -/
theorem store_step (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type) (ret : MachineData → Effects)
    (bs : List UInt8) (F : DataMem → Prop) (post : MachineState → Prop)
    (H : (Eq (bs.At addr) ⋆ F) s.dmem) (hl : bs.length = w.bytes)
    (k : ∀ m', (Eq ((Int.toBytes w.bytes v.toInt).At addr) ⋆ F) m' → (ret { s with dmem := m' }).All post) :
    (MachineData.store s addr v ret).All post := by
  rw [store_sep s addr w v ret bs F H hl, Effects.All_require_write_access]
  exact k _ (Mem.storeInt_sep addr w.bytes bs F s.dmem ⟨H, hl⟩ v.toInt)

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

/-- Unfold one instruction and normalize addresses; stops at `MachineData.load`/`store`. -/
macro "kunfold" : tactic => `(tactic| simp only [Directive.interp, Instr.interp, Operation.interp,
  Operand.interp, RegOrMem.interp, RelRegOrMem.interp, Fk.jmp_rel, AddrExpr.interp, ConstExpr.interp, MachineData.set,
  MachineData.setReg, Effects.All, Width.bits, Width.bytes, Int.add_zero, BitVec.setWidth_eq,
  Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset, BitVec.toAddressSize,
  BitVec.take, BitVec.drop, BitVec.signed, Fk.ofInt_toInt_add, Fk.ofInt_int64, Fk.extractLsb'_full,
  Nat.sub_zero, Int64.toBitVec_ofNat, UInt64.toBitVec_ofNat, BitVec.add_zero, Fk.add_ofNat_zero, Fk.add_lit_zero, Fk.add_ofInt_zero, Fk.add_int64_zero, Fk.rip_addr, Fk.rip_addr'])
