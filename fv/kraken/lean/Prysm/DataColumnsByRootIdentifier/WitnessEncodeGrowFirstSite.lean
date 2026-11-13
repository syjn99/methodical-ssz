import Prysm.DataColumnsByRootIdentifier.EncodeGrowFirstSite
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of `Encode.grow_first_site` (grow at site 1): n = 0, 1, 128

Host: data labels, the real Go 1.26.10 `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (index 8) and `MemmoveGrowsliceModel`
(index 126: `model_growslice`, new capacity 2·newLen + 192 from the bump heap, and `model_memmove`, both with S = 0).
`dst` has len 3321 and cap 3352 (`len + 32 > cap`, so site 1 grows); `nextSliceCap 3353 3352 = 4382`, which holds
`len + 36 + 8n` for n ≤ 128 (`hfit`). One memory block at `0x10000`: bump pointer, a 16956-byte bump heap
(= 2·4382 + 8192, the contract budget), guard word, receiver window (48 bytes), root (32), the 176-byte stack window
(rsp − 144 to rsp + 32, rsp = 0x1432c), `dst` (prefix 3321 zero bytes, 31 spare bytes) and the 8n column bytes.
Frame `R`: the receiver words not read, the stack gaps at rsp − 96 (32 bytes) and rsp − 48, and the spare bytes.
-/

open Machine Runtime Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowFirstSite


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
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev bitvec_word_bytes (v : BitVec 64) : List UInt8 := Int.toBytes 8 v.toInt

/-- bump pointer · heap · guard · receiver window (48) · root · rslot · spill (40) · gap (32) · l64 · l56 · gap ·
l40 · l32 · l24 · l16 · fp · return address · spills rax, rbx, rcx · prefix · spare · columns. -/
def block (root cb : List UInt8) (pc nb : BitVec 64) : List UInt8 :=
  bitvec_word_bytes 0x10008 ++ (zeros 16956 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x1427c ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes pc ++ (bitvec_word_bytes nb
    ++ (root ++ (zeros 8 ++ (zeros 40 ++ (zeros 32 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (bitvec_word_bytes 0
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 3321 ++ (zeros 31 ++ cb))))))))))))))))))))))))))

def mem (root cb : List UInt8) (pc nb : BitVec 64) : DataMem := (block root cb pc nb).At (0x10000 : BitVec 64)

def initial_state (root cb : List UInt8) (pc nb : BitVec 64) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1424c, 0x1434c, 3321, 0, 0, 3352, 0x1432c, 0, 0, 0, 0, 0, 0, 0, 0x14234, 0⟩, zmms, flags,
    mem root cb pc nb⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x10008 : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 16956).At (0x10008 : BitVec 64)) ⋆ X)) m) : (bumpHeap 16956 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x10008, by decide, by rw [label_bump_pointer]; exact hm⟩) h

theorem next_slice_cap_eq : nextSliceCap 3353 3352 = 4382 := by decide

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeGrowFirstSite`): 1000000 fails (`whnf` timeout); 4000000 passes. Profile (the 4000000 build): `simp` 10.2 s of
-- the declaration, the `sep_comm` sort of the memory premise (the cause of `Prysm/DataColumnsByRootIdentifier/WitnessEncodeFastPath.lean`).
set_option maxHeartbeats 4000000 in
-- maxRecDepth (builds at the default, 2000 and 20000, and a later run): 512 and 2000 fail; WitnessEncodeFastPath n = 128 passes at 4000, WitnessEncodeGrowFirstSite fails at 4000 and passes
-- at 8000 ("maximum recursion depth" at the declaration). Replacing `simp [initial_state]` by `dsimp only [initial_state]; decide`
-- did not remove it (one more run); the cause is not located. all three witnesses.
set_option maxRecDepth 8000 in
/-- n = 0: growslice runs at site 1; the encoder returns `rbx = 3321 + 36 + 8·0` and a capacity ≥ 4382. -/
theorem runs_empty (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 0)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 3321 + 36 + 8 * 0
        ∧ 4382 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x15064 0 zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb 0x15064 0 zmms flags) 0 0 0x1427c 0x15064 0 0
    rfl (by decide) root cb (zeros 3321) hroot (by rw [hcb]) rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 16956
    (Eq ((zeros 8).At (0x1424c : BitVec 64)) ⋆ Eq ((zeros 8).At (0x14264 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x142cc : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x142fc : BitVec 64)) ⋆ Eq ((zeros 31).At (0x15045 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x15064 0).At (0x10000 : BitVec 64)) (mem root cb 0x15064 0) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state])
    (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state root cb 0x15064 0 zmms flags).regs.rcx.toNat + 32)
        (initial_state root cb 0x15064 0 zmms flags).regs.rdi.toNat = 4382 := by simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeGrowFirstSite`): 1000000 fails (`whnf` timeout); 4000000 passes. Profile (the 4000000 build): `simp` 10.2 s of
-- the declaration, the `sep_comm` sort of the memory premise (the cause of `Prysm/DataColumnsByRootIdentifier/WitnessEncodeFastPath.lean`).
set_option maxHeartbeats 4000000 in
-- maxRecDepth (builds at the default, 2000 and 20000, and a later run): 512 and 2000 fail; WitnessEncodeFastPath n = 128 passes at 4000, WitnessEncodeGrowFirstSite fails at 4000 and passes
-- at 8000 ("maximum recursion depth" at the declaration). Replacing `simp [initial_state]` by `dsimp only [initial_state]; decide`
-- did not remove it (one more run); the cause is not located. all three witnesses.
set_option maxRecDepth 8000 in
/-- n = 1: growslice runs at site 1; the encoder returns `rbx = 3321 + 36 + 8·1` and a capacity ≥ 4382. -/
theorem runs_one_element (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 3321 + 36 + 8 * 1
        ∧ 4382 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x15064 1 zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb 0x15064 1 zmms flags) 0 0 0x1427c 0x15064 1 1
    rfl (by decide) root cb (zeros 3321) hroot (by rw [hcb]) rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 16956
    (Eq ((zeros 8).At (0x1424c : BitVec 64)) ⋆ Eq ((zeros 8).At (0x14264 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x142cc : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x142fc : BitVec 64)) ⋆ Eq ((zeros 31).At (0x15045 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x15064 1).At (0x10000 : BitVec 64)) (mem root cb 0x15064 1) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state])
    (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state root cb 0x15064 1 zmms flags).regs.rcx.toNat + 32)
        (initial_state root cb 0x15064 1 zmms flags).regs.rdi.toNat = 4382 := by simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeGrowFirstSite`): 1000000 fails (`whnf` timeout); 4000000 passes. Profile (the 4000000 build): `simp` 10.2 s of
-- the declaration, the `sep_comm` sort of the memory premise (the cause of `Prysm/DataColumnsByRootIdentifier/WitnessEncodeFastPath.lean`).
set_option maxHeartbeats 4000000 in
-- maxRecDepth (builds at the default, 2000 and 20000, and a later run): 512 and 2000 fail; WitnessEncodeFastPath n = 128 passes at 4000, WitnessEncodeGrowFirstSite fails at 4000 and passes
-- at 8000 ("maximum recursion depth" at the declaration). Replacing `simp [initial_state]` by `dsimp only [initial_state]; decide`
-- did not remove it (one more run); the cause is not located. all three witnesses.
set_option maxRecDepth 8000 in
/-- n = 128: growslice runs at site 1; the encoder returns `rbx = 3321 + 36 + 8·128` and a capacity ≥ 4382. -/
theorem runs_maximum (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 1024)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 3321 + 36 + 8 * 128
        ∧ 4382 ≤ st.data.regs.rcx.toNat ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x15064 128 zmms flags, Host.addrOf 8⟩ :=
  eventually_mono (Encode.grow_first_site 8 placed_at_8 labels_fresh_at_8 (initial_state root cb 0x15064 128 zmms flags) 0 0 0x1427c 0x15064 128 128
    rfl (by decide) root cb (zeros 3321) hroot (by rw [hcb]) rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 40) (zeros 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl bumpHeap 16956
    (Eq ((zeros 8).At (0x1424c : BitVec 64)) ⋆ Eq ((zeros 8).At (0x14264 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x142cc : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x142fc : BitVec 64)) ⋆ Eq ((zeros 31).At (0x15045 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x15064 128).At (0x10000 : BitVec 64)) (mem root cb 0x15064 128) := rfl
      witness_split [hroot, hcb]
      have H2 := lift_heap H
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state])
    (by simp only [initial_state]; decide) (by simp only [initial_state]; decide)
    (by unfold maxAlloc; omega) (model_growslice 126 placed_at_126 labels_fresh_at_126 _ 0) (model_memmove 126 placed_at_126 labels_fresh_at_126 0))
    (fun _ h => ⟨h.1, h.2.1, by
      have e : nextSliceCap ((initial_state root cb 0x15064 128 zmms flags).regs.rcx.toNat + 32)
        (initial_state root cb 0x15064 128 zmms flags).regs.rdi.toNat = 4382 := by simp only [initial_state]; decide
      have := h.2.2.1; omega,
      h.2.2.2.1, h.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_empty (zeros 32) [] rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_one_element ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 0x0123456789abcdef) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_maximum (List.replicate 32 0xff) (List.replicate 1024 0xff) (by decide) List.length_replicate z' f

end Prysm.DataColumnsByRootIdentifier.Witness.EncodeGrowFirstSite
