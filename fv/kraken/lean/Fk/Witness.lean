import Fk.LuAccept
import Fk.Bump

/-!
# Non-vacuity of `lu_accept_main` (B2.0)

A concrete `Host`: five data labels (`runtime.writeBarrier`, padding,
`runtime.fvBump`), then ListU64.UnmarshalSSZ at index 5, then the bump
allocator `BumpAlloc` (Fk/Bump.lean). Every directive has size 1, from address
0x10000. In this Host, for every n ≤ 16 and every input `bs` of 8n bytes,
`lu_accept_runs` gives a concrete machine state from which the real
ListU64.UnmarshalSSZ code returns with the receiver set: all premises of
`lu_accept_main`, including the makeslice contract (`bump_makeslice`), are
discharged by proofs. The three `example`s at the end instantiate n = 0, 1, 16.
-/

open Fk Fk.Code

namespace Fk.Witness

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def linkProg : Program := dataLabels ++ ListU64UnmarshalSSZ ++ BumpAlloc

theorem sizeBefore_one (P : Program) (j : Nat) :
    ((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ P).program.take j |>.map (·.size)).sum = min j P.length := by
  simp only [Kraken.Layout.apply]
  rw [List.map_take, show (List.mapIdx (fun _ d => ({ directive := d, size := 1 } : Kraken.Sized Directive)) P).map (·.size)
      = List.replicate P.length 1 by apply List.ext_getElem <;> simp]
  simp [List.take_replicate]

set_option maxRecDepth 100000 in
theorem linkProg_length : linkProg.length = 204 := by
  rfl

instance witnessHost : Host where
  prog := linkProg
  layout := ⟨0x10000, fun _ => 1⟩
  zero_inert := by intro i d _ h; simp at h
  addr_determines_offset := by
    intro j k h
    simp only [Kraken.Executable.addrOf, Kraken.Executable.sizeBefore] at h ⊢
    rw [sizeBefore_one] at h ⊢; rw [sizeBefore_one] at h ⊢
    rw [linkProg_length] at h ⊢
    have h' := congrArg Int64.toNatClampNeg ((Int64.add_right_inj _).mp h)
    rw [Int64.toNatClampNeg_ofNat_of_lt (by omega), Int64.toNatClampNeg_ofNat_of_lt (by omega)] at h'
    exact h'

theorem prog_eq : Host.prog = linkProg := rfl

theorem addrOf_eq (j : Nat) (hj : j ≤ 204) : Host.addrOf j = 0x10000 + Int64.ofNat j := by
  show (0x10000 : Int64) + Int64.ofNat (((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ linkProg).program.take j).map (·.size)).sum = _
  rw [sizeBefore_one, linkProg_length, Nat.min_eq_left hj]

theorem hk5 : ListU64UnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc, by simp [linkProg, dataLabels]⟩

theorem hk198 : BumpAlloc.IsInfixAt Host.prog 198 := by
  rw [prog_eq]
  have h : (dataLabels ++ ListU64UnmarshalSSZ).length = 198 := by
    rw [List.length_append, show ListU64UnmarshalSSZ.length = 193 from by rfl]; rfl
  exact ⟨[], by rw [linkProg, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem notin_lu (l : Label) (hl : l ∈ ["runtime.writeBarrier", "pad1", "pad2", "pad3", "runtime.fvBump", "runtime.makeslice"]) :
    Kraken.Directive.label l ∉ ListU64UnmarshalSSZ := by
  intro hm
  have hc := (@List.contains_iff_mem _ instBEqOfDecidableEq _ _ _).mpr hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ListU64UnmarshalSSZ, List.contains_cons, List.contains_nil] at hc <;> revert hc <;> decide

theorem hf5 : LabelsFresh ListU64UnmarshalSSZ 5 := by
  intro i hi l hp
  rw [prog_eq] at hp
  apply notin_lu
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [linkProg, dataLabels] at hp <;> subst hp <;> simp

theorem hf198 : ∀ i < 198, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  intro i hi hp
  rw [prog_eq, linkProg, List.getElem?_append_left (by simp [dataLabels]; rw [show ListU64UnmarshalSSZ.length = 193 from by rfl]; omega)] at hp
  rcases List.mem_append.mp (List.mem_of_getElem? hp) with h | h
  · simp [dataLabels] at h
  · exact notin_lu "runtime.makeslice" (by simp) h

theorem label_wb : label "runtime.writeBarrier" = 0x10000 := by
  rw [label_eq_addrOf (j := 0) (by rw [prog_eq]; rfl) (by intro i hi; omega), addrOf_eq 0 (by omega)]; rfl

theorem label_bump : label "runtime.fvBump" = 0x10004 := by
  rw [label_eq_addrOf (j := 4) (by rw [prog_eq]; rfl)
    (by intro i hi; rw [prog_eq]; have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
        rcases this with rfl | rfl | rfl | rfl <;> simp [linkProg, dataLabels]), addrOf_eq 4 (by omega)]; rfl

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

/-- The whole data memory, from 0x10000: write-barrier flag, bump pointer, heap
(128 bytes), stack guard, stack frame (with gaps), receiver, input. -/
def block (bs : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ (Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ (z 128 ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt
    ++ (z 8 ++ (z 40 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 64 ++ (z 8 ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt
    ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ ([4, 0, 0, 0] ++ bs)))))))))))))))))

def blockMem (bs : List UInt8) : DataMem := (block bs).At (0x10000 : BitVec 64)

def s0 (n : Nat) (bs : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1013c, 0x10154, UInt64.ofNat (4 + 8 * n), 0, 0, UInt64.ofNat (4 + 8 * n), 0x10124, 0,
    0, 0, 0, 0, 0, 0, 0x1007c, 0⟩, zmms, flags, blockMem bs⟩

theorem nil_At_emp (a : BitVec 64) : Eq (([] : List UInt8).At a) = Std.ExtHashMap.emp := by
  funext m; apply propext; simp only [List.At, List.mapIdx_nil, Std.ExtHashMap.ofList_nil, Std.ExtHashMap.emp]
  exact ⟨Eq.symm, Eq.symm⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem witness_mem (n : Nat) (bs : List UInt8) (hbs : bs.length = 8 * n) (hn : n ≤ 16)
    (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 n bs zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 88)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ bumpHeap 128
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ (Eq (bs.At (s.regs.rbx.toBitVec + 4))
        ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16))
        ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True) := by
  intro s
  have H : Eq ((block bs).At (0x10000 : BitVec 64)) (blockMem bs) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : ((Eq ((Int.toBytes 8 (65548#64).toInt).At 65540#64) ⋆ Eq ((z 128).At 65548#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65676#64) ⋆ Eq ((z 8).At 65684#64)
        ⋆ Eq ((z 40).At 65692#64) ⋆ Eq ((z 8).At 65732#64) ⋆ Eq ((z 8).At 65740#64) ⋆ Eq ((z 8).At 65748#64)
        ⋆ Eq ((z 64).At 65756#64) ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64)
        ⋆ Eq ((z 8).At 65836#64) ⋆ Eq ((z 8).At 65844#64) ⋆ Eq ((z 8).At 65852#64) ⋆ Eq ((z 8).At 65860#64)
        ⋆ Eq ((z 8).At 65868#64) ⋆ Eq ([4, 0, 0, 0].At 65876#64) ⋆ Eq (bs.At 65880#64)))
      (blockMem bs) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 128) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  have H4 : (Eq ((z 40).At 65692#64) ⋆ Eq ((z 64).At 65756#64)
      ⋆ (bumpHeap 128 ⋆ Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65676#64) ⋆ Eq ((z 8).At 65684#64)
        ⋆ Eq ((z 8).At 65732#64) ⋆ Eq ((z 8).At 65740#64) ⋆ Eq ((z 8).At 65748#64)
        ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64)
        ⋆ Eq ((z 8).At 65836#64) ⋆ Eq ((z 8).At 65844#64) ⋆ Eq ((z 8).At 65852#64) ⋆ Eq ((z 8).At 65860#64)
        ⋆ Eq ((z 8).At 65868#64) ⋆ Eq ([4, 0, 0, 0].At 65876#64) ⋆ Eq (bs.At 65880#64)))
      (blockMem bs) := by ecancel
  have H5 := sep_mono_left (P' := fun _ => True) (fun _ _ => trivial) H4
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H5 ⊢
  have H6 : (Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64) ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((z 8).At 65732#64)
      ⋆ Eq ((z 8).At 65740#64) ⋆ Eq ((z 8).At 65748#64) ⋆ Eq ((z 8).At 65836#64) ⋆ Eq ((z 8).At 65844#64)
      ⋆ Eq ((z 8).At 65684#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65676#64)
      ⋆ bumpHeap 128 ⋆ Eq ([4, 0, 0, 0].At 65876#64)
      ⋆ (Eq (bs.At 65880#64) ⋆ Eq ((z 8).At 65852#64) ⋆ Eq ((z 8).At 65860#64) ⋆ Eq ((z 8).At 65868#64)
        ⋆ Eq ([0, 0, 0, 0].At 65536#64) ⋆ T)) (blockMem bs) := by ecancel
  exact H6

/-- **Non-vacuity.** In `witnessHost`, from the state `s0 n bs`, the real
ListU64.UnmarshalSSZ code (index 5) runs to its return address and returns nil
(`lu_accept_main` gives the receiver and memory). Every premise of `lu_accept_main` is proved here, the
makeslice contract by `bump_makeslice`. -/
theorem lu_accept_runs (n : Nat) (hn : n ≤ 16) (bs : List UInt8) (hbs : bs.length = 8 * n)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨s0 n bs zmms flags, Host.addrOf 5⟩ :=
  eventually_trans _ _ _ _ (lu_accept_main 5 hk5 hf5 bs n hbs hn (s0 n bs zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] rfl bumpHeap 128 (witness_mem n bs hbs hn zmms flags)
    (by simp [s0]) (by simp [s0]) (by simp [s0]; omega) (by simp [s0]) (by simp [s0]; omega) (by omega)
    (bump_makeslice 198 hk198 hf198 _))
    (fun _ h => Eventually.done _ ⟨h.1, h.2.1, h.2.2.1⟩)

/-- The three sizes the brief names: empty, one element, sixteen (the maximum). -/
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 0 (by omega) [] rfl z f
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 1 (by omega) (List.replicate 8 7) rfl z f
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 16 (by omega) (List.replicate 128 255) rfl z f

end Fk.Witness
