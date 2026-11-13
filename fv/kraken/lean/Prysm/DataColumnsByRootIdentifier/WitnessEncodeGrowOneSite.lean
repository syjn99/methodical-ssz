import Prysm.DataColumnsByRootIdentifier.EncodeGrowOneSite
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of `Encode.grow_one_site` (one-growth path: growth at any one site)

One instance per growth site (see each namespace): site 1, site 2 and the loop. In each case the first growth gives
`nextSliceCap ≥ len + 36 + 8n` (`hone`: the doubling rule `next_slice_cap_double` below 256, one round of `growLoop` `next_slice_cap_one_step`
above). Host: data labels, the real Go 1.26.10 `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (index 8),
`MemmoveGrowsliceModel` (index 126: `model_growslice`, `model_memmove`). The layout of `Prysm/DataColumnsByRootIdentifier/WitnessEncodeGrowFirstSite.lean` plus the slots x − 48, x − 72 and the
old block `pre ‖ spare`. Frame `R`: the receiver words the code does not read and the 24-byte gap at rsp − 96.
-/

open Machine Runtime Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowOneSite

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7"]

def program : Program := dataLabels ++ marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 152 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_8 : marshalSSZTo.IsInfixAt Host.prog 8 :=
  infixAt_of dataLabels MemmoveGrowsliceModel (by simp [host_program_eq, program, List.append_assoc]) rfl
theorem placed_at_126 : MemmoveGrowsliceModel.IsInfixAt Host.prog 126 :=
  infixAt_of (dataLabels ++ marshalSSZTo) [] (by simp [host_program_eq, program, List.append_assoc]) (by rfl)
theorem labels_fresh_at_8 : LabelsFresh marshalSSZTo 8 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_126 : LabelsFresh MemmoveGrowsliceModel 126 := labelsFresh_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [labs])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev bitvec_word_bytes (v : BitVec 64) : List UInt8 := Int.toBytes 8 v.toInt

/-- `nextSliceCap m cap` for `cap ≥ 256`, `cap < m ≤ 2·cap` and `m ≤ cap + (cap + 768)/4`: one round of `growLoop`. -/
theorem next_slice_cap_one_step (m cap : Nat) (h1 : 256 ≤ cap) (h2 : cap < m) (h3 : m ≤ cap + (cap + 768) / 4) (h4 : m ≤ 2 * cap) :
    nextSliceCap m cap = cap + (cap + 768) / 4 := by
  unfold nextSliceCap
  rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨f, rfl⟩ : ∃ f, m = f + 1 := ⟨m - 1, by omega⟩
  simp only [growLoop]
  rw [if_pos h3]

/-- `nextSliceCap m cap` for `cap < 256` and `cap < m ≤ 2·cap`: the doubling rule. -/
theorem next_slice_cap_double (m cap : Nat) (h1 : cap < 256) (h2 : cap < m) (h4 : m ≤ 2 * cap) : nextSliceCap m cap = 2 * cap := by
  unfold nextSliceCap
  rw [if_neg (by omega), if_pos h1]

namespace FirstSite

/-- n = 1, len 100, cap 120. bump pointer · heap (9152) · guard · receiver window · root · rslot · spill · gap (24) ·
l72 … l16 · fp · return address · spills · pre · spare · columns. -/
def block (root cb : List UInt8) : List UInt8 :=
  bitvec_word_bytes 0x10008 ++ (zeros 9152 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x12400 ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes 0x12548 ++ (bitvec_word_bytes 1
    ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100 ++ (zeros 20 ++ cb)))))))))))))))))))))))))))

def initial_state (root cb : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x123d0, 0x124d0, 100, 0, 0, 120, 0x124b0, 0, 0, 0, 0, 0, 0, 0, 0x123b8, 0⟩, zmms, flags,
    (block root cb).At (0x10000 : BitVec 64)⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 9152).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9152 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured: maxHeartbeats 1000000 fails at `whnf` (the `simp` sort of the memory premise), 4000000
-- passes; maxRecDepth 8000 passes here except for `loop128` (8000 fails, 32000 passes; 16000 not decided).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem runs (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 100 + 36 + 8 * 1
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_one_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb zmms flags) 0 0 0x12400 0x12548 1 1
    rfl (by decide) root cb (zeros 100) (zeros 20) hroot (by rw [hcb]) rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 9152
    (Eq ((zeros 8).At (0x123d0 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x123e8 : BitVec 64)) ⋆ Eq ((zeros 24).At (0x12450 : BitVec 64)))
    (by
      have H : Eq ((block root cb).At (0x10000 : BitVec 64)) ((block root cb).At (0x10000 : BitVec 64)) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      rw [Mem.At_append_sep (zeros 100) (zeros 20) _ (by simp)]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat, List.length_replicate,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by dsimp only [initial_state]; decide) (by dsimp only [initial_state]; decide) (by unfold maxAlloc; omega)
    (by
      intro m hm hc
      dsimp only [initial_state] at hm hc ⊢
      simp only [show (UInt64.toNat 100) = 100 from rfl, show (UInt64.toNat 120) = 120 from rfl] at hm hc ⊢
      rw [next_slice_cap_double m 120 (by omega) (by omega) (by omega)]; omega)
    (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)

end FirstSite

namespace SecondSite

/-- n = 0, len 100, cap 134. bump pointer · heap (9120) · guard · receiver window · root · rslot · spill · gap (24) ·
l72 … l16 · fp · return address · spills · pre · spare · columns. -/
def block (root cb : List UInt8) : List UInt8 :=
  bitvec_word_bytes 0x10008 ++ (zeros 9120 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x123e0 ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes 0x12536 ++ (bitvec_word_bytes 0
    ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100 ++ (zeros 34 ++ cb)))))))))))))))))))))))))))

def initial_state (root cb : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x123b0, 0x124b0, 100, 0, 0, 134, 0x12490, 0, 0, 0, 0, 0, 0, 0, 0x12398, 0⟩, zmms, flags,
    (block root cb).At (0x10000 : BitVec 64)⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 9120).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9120 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured: maxHeartbeats 1000000 fails at `whnf` (the `simp` sort of the memory premise), 4000000
-- passes; maxRecDepth 8000 passes here except for `loop128` (8000 fails, 32000 passes; 16000 not decided).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem runs (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 0)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 100 + 36 + 8 * 0
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_one_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb zmms flags) 0 0 0x123e0 0x12536 0 0
    rfl (by decide) root cb (zeros 100) (zeros 34) hroot (by rw [hcb]) rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 9120
    (Eq ((zeros 8).At (0x123b0 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x123c8 : BitVec 64)) ⋆ Eq ((zeros 24).At (0x12430 : BitVec 64)))
    (by
      have H : Eq ((block root cb).At (0x10000 : BitVec 64)) ((block root cb).At (0x10000 : BitVec 64)) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      rw [Mem.At_append_sep (zeros 100) (zeros 34) _ (by simp)]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat, List.length_replicate,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by dsimp only [initial_state]; decide) (by dsimp only [initial_state]; decide) (by unfold maxAlloc; omega)
    (by
      intro m hm hc
      dsimp only [initial_state] at hm hc ⊢
      simp only [show (UInt64.toNat 100) = 100 from rfl, show (UInt64.toNat 134) = 134 from rfl] at hm hc ⊢
      rw [next_slice_cap_double m 134 (by omega) (by omega) (by omega)]; omega)
    (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)

end SecondSite

namespace LoopSixteenElements

/-- n = 16, len 100, cap 200. bump pointer · heap (9632) · guard · receiver window · root · rslot · spill · gap (24) ·
l72 … l16 · fp · return address · spills · pre · spare · columns. -/
def block (root cb : List UInt8) : List UInt8 :=
  bitvec_word_bytes 0x10008 ++ (zeros 9632 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x125e0 ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes 0x12778 ++ (bitvec_word_bytes 16
    ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 100 ++ (zeros 100 ++ cb)))))))))))))))))))))))))))

def initial_state (root cb : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x125b0, 0x126b0, 100, 0, 0, 200, 0x12690, 0, 0, 0, 0, 0, 0, 0, 0x12598, 0⟩, zmms, flags,
    (block root cb).At (0x10000 : BitVec 64)⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 9632).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 9632 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured: maxHeartbeats 1000000 fails at `whnf` (the `simp` sort of the memory premise), 4000000
-- passes; maxRecDepth 8000 passes here except for `loop128` (8000 fails, 32000 passes; 16000 not decided).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
theorem runs (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 128)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 100 + 36 + 8 * 16
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_one_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb zmms flags) 0 0 0x125e0 0x12778 16 16
    rfl (by decide) root cb (zeros 100) (zeros 100) hroot (by rw [hcb]) rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 9632
    (Eq ((zeros 8).At (0x125b0 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x125c8 : BitVec 64)) ⋆ Eq ((zeros 24).At (0x12630 : BitVec 64)))
    (by
      have H : Eq ((block root cb).At (0x10000 : BitVec 64)) ((block root cb).At (0x10000 : BitVec 64)) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      rw [Mem.At_append_sep (zeros 100) (zeros 100) _ (by simp)]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat, List.length_replicate,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by dsimp only [initial_state]; decide) (by dsimp only [initial_state]; decide) (by unfold maxAlloc; omega)
    (by
      intro m hm hc
      dsimp only [initial_state] at hm hc ⊢
      simp only [show (UInt64.toNat 100) = 100 from rfl, show (UInt64.toNat 200) = 200 from rfl] at hm hc ⊢
      rw [next_slice_cap_double m 200 (by omega) (by omega) (by omega)]; omega)
    (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)

end LoopSixteenElements

namespace LoopMaximumElements

/-- n = 128, len 2000, cap 2548. bump pointer · heap (20816) · guard · receiver window · root · rslot · spill · gap (24) ·
l72 … l16 · fp · return address · spills · pre · spare · columns. -/
def block (root cb : List UInt8) : List UInt8 :=
  bitvec_word_bytes 0x10008 ++ (zeros 20816 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x15190 ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes 0x15c54 ++ (bitvec_word_bytes 128
    ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 2000 ++ (zeros 548 ++ cb)))))))))))))))))))))))))))

def initial_state (root cb : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x15160, 0x15260, 2000, 0, 0, 2548, 0x15240, 0, 0, 0, 0, 0, 0, 0, 0x15148, 0⟩, zmms, flags,
    (block root cb).At (0x10000 : BitVec 64)⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 20816).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 20816 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

-- Measured: maxHeartbeats 1000000 fails at `whnf` (the `simp` sort of the memory premise), 4000000
-- passes; maxRecDepth 8000 passes here except for `loop128` (8000 fails, 32000 passes; 16000 not decided).
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 32000 in
theorem runs (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 1024)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 2000 + 36 + 8 * 128
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_one_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb zmms flags) 0 0 0x15190 0x15c54 128 128
    rfl (by decide) root cb (zeros 2000) (zeros 548) hroot (by rw [hcb]) rfl rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 20816
    (Eq ((zeros 8).At (0x15160 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x15178 : BitVec 64)) ⋆ Eq ((zeros 24).At (0x151e0 : BitVec 64)))
    (by
      have H : Eq ((block root cb).At (0x10000 : BitVec 64)) ((block root cb).At (0x10000 : BitVec 64)) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      rw [Mem.At_append_sep (zeros 2000) (zeros 548) _ (by simp)]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat, List.length_replicate,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by dsimp only [initial_state]; decide) (by dsimp only [initial_state]; decide) (by unfold maxAlloc; omega)
    (by
      intro m hm hc
      dsimp only [initial_state] at hm hc ⊢
      simp only [show (UInt64.toNat 2000) = 2000 from rfl, show (UInt64.toNat 2548) = 2548 from rfl] at hm hc ⊢
      rw [next_slice_cap_one_step m 2548 (by omega) (by omega) (by omega) (by omega)]; omega)
    (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1⟩)

end LoopMaximumElements

end Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowOneSite
