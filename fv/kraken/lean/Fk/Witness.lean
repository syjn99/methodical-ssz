import Fk.LuAccept
import Fk.Bump
import Fk.RtCopy

/-!
# Non-vacuity of `lu_accept_main`

A concrete `Host`: five data labels (`runtime.writeBarrier`, padding,
`runtime.fvBump`), then ListU64.UnmarshalSSZ at index 5, then the bump
allocator `BumpAlloc` (Fk/Bump.lean).
-/

open Fk Fk.Code

namespace Fk.Witness

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def linkProg : Program := dataLabels ++ ListU64UnmarshalSSZ ++ BumpAlloc ++ RtCopy

theorem sizeBefore_one (P : Program) (j : Nat) :
    ((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ P).program.take j |>.map (·.size)).sum = min j P.length := by
  simp only [Kraken.Layout.apply]
  rw [List.map_take, show (List.mapIdx (fun _ d => ({ directive := d, size := 1 } : Kraken.Sized Directive)) P).map (·.size)
      = List.replicate P.length 1 by apply List.ext_getElem <;> simp]
  simp [List.take_replicate]

set_option maxRecDepth 100000 in
theorem linkProg_length : linkProg.length = 230 := by
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

theorem addrOf_eq (j : Nat) (hj : j ≤ 230) : Host.addrOf j = 0x10000 + Int64.ofNat j := by
  show (0x10000 : Int64) + Int64.ofNat (((Kraken.Layout.apply ⟨0x10000, fun _ => 1⟩ linkProg).program.take j).map (·.size)).sum = _
  rw [sizeBefore_one, linkProg_length, Nat.min_eq_left hj]

theorem hk5 : ListU64UnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc ++ RtCopy, by simp [linkProg, dataLabels]⟩

theorem hk198 : BumpAlloc.IsInfixAt Host.prog 198 := by
  rw [prog_eq]
  have h : (dataLabels ++ ListU64UnmarshalSSZ).length = 198 := by
    rw [List.length_append, show ListU64UnmarshalSSZ.length = 193 from by rfl]; rfl
  exact ⟨RtCopy, by rw [linkProg, List.append_assoc, ← h, List.drop_left]⟩

theorem len204 : (dataLabels ++ ListU64UnmarshalSSZ ++ BumpAlloc).length = 204 := by
  rw [List.length_append, List.length_append, show ListU64UnmarshalSSZ.length = 193 from by rfl]; rfl

theorem hk204 : RtCopy.IsInfixAt Host.prog 204 := by
  rw [prog_eq]
  have h := len204
  exact ⟨[], by rw [linkProg, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem notin_lu (l : Label) (hl : l ∈ ["runtime.writeBarrier", "pad1", "pad2", "pad3", "runtime.fvBump", "runtime.makeslice",
    "runtime.memmove", "runtime.growslice", "L_fvcopy", "L_fvcopy_loop", "L_fvcopy_done"]) :
    Kraken.Directive.label l ∉ ListU64UnmarshalSSZ := by
  intro hm
  have hc := (@List.contains_iff_mem _ instBEqOfDecidableEq _ _ _).mpr hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ListU64UnmarshalSSZ, List.contains_cons, List.contains_nil] at hc <;> revert hc <;> decide

theorem hf5 : LabelsFresh ListU64UnmarshalSSZ 5 := by
  intro i hi l hp
  rw [prog_eq] at hp
  apply notin_lu
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> simp [linkProg, dataLabels] at hp <;> subst hp <;> simp

theorem hf198 : ∀ i < 198, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  intro i hi hp
  rw [prog_eq, linkProg, List.getElem?_append_left (by rw [len204]; omega), List.getElem?_append_left (by simp [dataLabels]; rw [show ListU64UnmarshalSSZ.length = 193 from by rfl]; omega)] at hp
  rcases List.mem_append.mp (List.mem_of_getElem? hp) with h | h
  · simp [dataLabels] at h
  · exact notin_lu "runtime.makeslice" (by simp) h

set_option maxRecDepth 100000 in
/-- No label of `RtCopy` occurs before it (index 204). -/
theorem hf204 : LabelsFresh RtCopy 204 := by
  intro i hi l hp hr
  rw [prog_eq, linkProg, List.getElem?_append_left (by rw [len204]; omega)] at hp
  have hl : l ∈ ["runtime.memmove", "runtime.growslice", "L_fvcopy", "L_fvcopy_loop", "L_fvcopy_done"] := by
    simp only [RtCopy, List.mem_cons, Kraken.Directive.label.injEq, reduceCtorEq, false_or, List.not_mem_nil,
      or_false] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hr with h | h | h | h | h <;> simp [h]
  rcases List.mem_append.mp (List.mem_of_getElem? hp) with h | h
  · rcases List.mem_append.mp h with h | h
    · simp [dataLabels] at h; simp at hl; rcases h with rfl | rfl | rfl | rfl | rfl <;> simp at hl
    · exact notin_lu l (by simp at hl ⊢; rcases hl with h | h | h | h | h <;> simp [h]) h
  · simp [BumpAlloc] at h; subst h; simp at hl

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
    ++ (z 8 ++ (z 24 ++ (z 16 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 64 ++ (z 8 ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt
    ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ (z 8 ++ ([4, 0, 0, 0] ++ bs))))))))))))))))))

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
      ⋆ Eq ((z 24).At (s.regs.rsp.toBitVec - 136))
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
        ⋆ Eq ((z 24).At 65692#64) ⋆ Eq ((z 16).At 65716#64) ⋆ Eq ((z 8).At 65732#64) ⋆ Eq ((z 8).At 65740#64) ⋆ Eq ((z 8).At 65748#64)
        ⋆ Eq ((z 64).At 65756#64) ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64)
        ⋆ Eq ((z 8).At 65836#64) ⋆ Eq ((z 8).At 65844#64) ⋆ Eq ((z 8).At 65852#64) ⋆ Eq ((z 8).At 65860#64)
        ⋆ Eq ((z 8).At 65868#64) ⋆ Eq ([4, 0, 0, 0].At 65876#64) ⋆ Eq (bs.At 65880#64)))
      (blockMem bs) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 128) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  have H4 : (Eq ((z 16).At 65716#64) ⋆ Eq ((z 64).At 65756#64)
      ⋆ (bumpHeap 128 ⋆ Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65676#64) ⋆ Eq ((z 8).At 65684#64)
        ⋆ Eq ((z 24).At 65692#64) ⋆ Eq ((z 8).At 65732#64) ⋆ Eq ((z 8).At 65740#64) ⋆ Eq ((z 8).At 65748#64)
        ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64)
        ⋆ Eq ((z 8).At 65836#64) ⋆ Eq ((z 8).At 65844#64) ⋆ Eq ((z 8).At 65852#64) ⋆ Eq ((z 8).At 65860#64)
        ⋆ Eq ((z 8).At 65868#64) ⋆ Eq ([4, 0, 0, 0].At 65876#64) ⋆ Eq (bs.At 65880#64)))
      (blockMem bs) := by ecancel
  have H5 := sep_mono_left (P' := fun _ => True) (fun _ _ => trivial) H4
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H5 ⊢
  have H6 : (Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65828#64) ⋆ Eq ((z 24).At 65692#64) ⋆ Eq ((z 8).At 65820#64) ⋆ Eq ((z 8).At 65732#64)
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
    (fun _ => True) 0 [] (z 24) rfl rfl bumpHeap 128 (witness_mem n bs hbs hn zmms flags)
    (by simp [s0]) (by simp [s0]) (by simp [s0]; omega) (by simp [s0]) (by simp [s0]; omega) (by omega)
    (bump_makeslice 198 hk198 hf198 _))
    (fun _ h => Eventually.done _ ⟨h.1, h.2.1, h.2.2.1⟩)

/-- The three sizes the brief names: empty, one element, sixteen (the maximum). -/
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 0 (by omega) [] rfl z f
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 1 (by omega) (List.replicate 8 7) rfl z f
example (z : RegZmms) (f : StatusFlags) := lu_accept_runs 16 (by omega) (List.replicate 128 255) rfl z f

/-! ## `GrowsliceC`

In the same Host, `rt_growslice 204` proves `GrowsliceC bumpHeap ty 1 0`.
`growslice_call_runs` gives a concrete state that satisfies every premise of
the contract for any old bytes `old`, `old.length ≤ oc < n ≤ 1000`, and runs
the call to its return. The examples are the BitL shape (`old = []`,
`oldCap = 0`, n = 1 and n = 257, the BitL maximum) and the ListU64 shape
(3 old bytes, cap 3, newLen 7). `review1b_input_excluded`: the review's input
(`newLen = 2^63`) does not meet the budget premise. -/

/-- Data memory for the growslice call, from 0x10000: write-barrier flag, bump
pointer, heap (12576 bytes), return slot, spill (40), old bytes. -/
def gblock (ret : Int64) (old : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ (Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ (z 12576 ++ (Int.toBytes 8 ret.toBitVec.toInt
    ++ (z 40 ++ old))))

def gMem (ret : Int64) (old : List UInt8) : DataMem := (gblock ret old).At (0x10000 : BitVec 64)

def gs0 (ret : Int64) (old : List UInt8) (oc n : Nat) (ty : BitVec 64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1315c, UInt64.ofNat n, UInt64.ofNat oc, 0, UInt64.ofBitVec ty, UInt64.ofNat (n - old.length), 0x1312c, 0,
    0, 0, 0, 0, 0, 0, 0, 0⟩, zmms, flags, gMem ret old⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem gs_mem (ret : Int64) (old : List UInt8) (hol : old.length ≤ 1000) :
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At (0x1312c : BitVec 64)) ⋆ Eq (([] : List UInt8).At ((0x1312c : BitVec 64) - BitVec.ofNat 64 0))
      ⋆ Eq ((z 40).At ((0x1312c : BitVec 64) + 8)) ⋆ Eq (old.At (0x1315c : BitVec 64)) ⋆ bumpHeap 12576
      ⋆ Eq ([0, 0, 0, 0].At (0x10000 : BitVec 64))) (gMem ret old) := by
  have H : Eq ((gblock ret old).At (0x10000 : BitVec 64)) (gMem ret old) := rfl
  conv at H => lhs; unfold gblock
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : ((Eq ((Int.toBytes 8 (65548#64).toInt).At 65540#64) ⋆ Eq ((z 12576).At 65548#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64) ⋆ Eq ((Int.toBytes 8 ret.toBitVec.toInt).At 78124#64)
        ⋆ Eq ((z 40).At 78132#64) ⋆ Eq (old.At 78172#64))) (gMem ret old) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 12576) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, nil_At_emp, Std.ExtHashMap.sep_emp]
  have e : ∀ A B C D E : DataMem → Prop, (A ⋆ (B ⋆ C ⋆ D ⋆ E)) = (C ⋆ D ⋆ E ⋆ A ⋆ B) := by
    intro A B C D E; ac_rfl
  rw [e] at H3; exact H3

/-- **Non-vacuity of `GrowsliceC`.** From `gs0`, the growslice model returns to
`ret` with rbx = n, a capacity of at least n, and the old bytes at the start of
the new block. Every premise of the contract is discharged. -/
theorem growslice_call_runs (ret : Int64) (old : List UInt8) (oc n : Nat) (h1 : old.length ≤ oc) (h2 : oc < n)
    (h3 : n ≤ 1000) (ty : BitVec 64) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ret ∧ st.data.regs.rbx.toNat = n ∧ n ≤ st.data.regs.rcx.toNat ∧
        ∃ tail : List UInt8, (Eq ((old ++ tail).At st.data.regs.rax.toBitVec) ⋆ fun _ => True) st.data.dmem)
      ⟨gs0 ret old oc n ty zmms flags, label "runtime.growslice"⟩ := by
  have hn : (UInt64.ofNat n).toNat = n := by simp; omega
  have hoc : (UInt64.ofNat oc).toNat = oc := by simp; omega
  have hdi : (UInt64.ofNat (n - old.length)).toNat = n - old.length := by simp; omega
  have hnc := nextSliceCap_le n oc h2
  refine eventually_mono (rt_growslice 204 hk204 hf204 ty 0 (gs0 ret old oc n ty zmms flags) ret old [] (z 40) 12576
    (Eq ([0, 0, 0, 0].At (0x10000 : BitVec 64))) (by decide) (by simp [gs0])
    (by simp only [gs0, hn, hdi]; omega) (by simp only [gs0, hn, hdi, hoc]; omega) (by simp only [gs0, hn, hoc]; omega)
    (by simp only [gs0, hn, hoc]; omega) (by unfold maxAlloc; omega) (by simp only [gs0, hn, hdi]; omega) rfl (by simp)
    (gs_mem ret old (by omega))) ?_
  rintro st ⟨hpc, -, -, -, hrbx, hnc1, -, stk', spl', tail, av', -, -, -, -, hm⟩
  refine ⟨hpc, by rw [hrbx]; exact hn, ?_, tail, sep_true (by ecancel)⟩
  have := nextSliceCap_ge n oc
  simp only [gs0, hn, hoc] at hnc1; omega

example (r : Int64) (ty : BitVec 64) (z : RegZmms) (f : StatusFlags) := growslice_call_runs r [] 0 1 (by simp) (by omega) (by omega) ty z f
example (r : Int64) (ty : BitVec 64) (z : RegZmms) (f : StatusFlags) := growslice_call_runs r [] 0 257 (by simp) (by omega) (by omega) ty z f
example (r : Int64) (ty : BitVec 64) (z : RegZmms) (f : StatusFlags) := growslice_call_runs r [1, 2, 3] 3 7 (by simp) (by omega) (by omega) ty z f

theorem review1b_input_excluded (esz oc avail : Nat) (he : 0 < esz) :
    ¬ (2 * (esz * nextSliceCap (2 ^ 63) oc) + 8192 ≤ avail ∧ avail ≤ maxAlloc) := by
  rintro ⟨h1, h2⟩
  have := nextSliceCap_ge (2 ^ 63) oc
  have : nextSliceCap (2 ^ 63) oc ≤ esz * nextSliceCap (2 ^ 63) oc := Nat.le_mul_of_pos_left _ he
  unfold maxAlloc at h2; omega

end Fk.Witness
