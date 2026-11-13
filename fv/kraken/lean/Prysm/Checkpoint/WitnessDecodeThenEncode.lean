import Prysm.Checkpoint.DecodeThenEncode
import Runtime.CopyModel
import Runtime.BumpAllocatorVariants
import Machine.WitnessHost
import Prysm.Checkpoint.GoValue

/-!
# Witness of `DecodeThenEncode.round_trip` (machine-level composition, one Host for decoder and encoder)

Host: data labels, the real Go 1.26.10 `(*v1alpha1.Checkpoint).UnmarshalSSZ`
(index 9), the real `(*primitives.Epoch).UnmarshalSSZ` (index 117), the 1-byte
bump `runtime.makeslice` (index 180, `bump_makeslice1`), `MemmoveGrowsliceModel` (index 186,
`model_memmove`) and the real `(*v1alpha1.Checkpoint).MarshalSSZTo` (index 212).
One memory block at `0x10000`: bump pointer, writeBarrier word, the 32-byte
heap, guard word, the 40 input bytes, the 72-byte receiver (all zero: a fresh
`&Checkpoint{}`), the 144-byte stack window (rsp = 0x1011c, decoder scratch
`S = 24`, encoder scratch 0) and `dst` at 0x10134 = prefix `[0xaa, 0xbb, 0xcc]`,
40 old bytes, 5 spare bytes (`cap = 48`). The frame `frame_rest` is the spare capacity.
The middle state is a real memory: the decoder's final memory with the
encoder's return address (`ra2 = 0`) stored into the return slot
(`Mem.storeInt`).
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.DecodeThenEncode

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.modelBumpPointer", .label "pad1", .label "pad2", .label "pad3", .label "pad4", .label "pad5",
   .label "pad6", .label "pad7", .label "runtime.writeBarrier"]

def program : Program := dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel ++ marshalSSZTo

theorem program_length : program.length = 303 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem host_program_eq : Host.prog = program := rfl

theorem placed_at_9 : unmarshalSSZ.IsInfixAt Host.prog 9 :=
  infixAt_of dataLabels (Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel ++ marshalSSZTo) (by simp [host_program_eq, program, List.append_assoc]) rfl

theorem placed_at_117 : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog 117 :=
  infixAt_of (dataLabels ++ unmarshalSSZ) (BumpMakeslice1 ++ MemmoveGrowsliceModel ++ marshalSSZTo) (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)

theorem placed_at_180 : BumpMakeslice1.IsInfixAt Host.prog 180 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ) (MemmoveGrowsliceModel ++ marshalSSZTo) (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)

theorem placed_at_186 : MemmoveGrowsliceModel.IsInfixAt Host.prog 186 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1) marshalSSZTo (by simp [host_program_eq, program, List.append_assoc])
    (by rfl)

theorem placed_at_212 : marshalSSZTo.IsInfixAt Host.prog 212 :=
  infixAt_of (dataLabels ++ unmarshalSSZ ++ Prysm.Epoch.Code.unmarshalSSZ ++ BumpMakeslice1 ++ MemmoveGrowsliceModel) []
    (by simp [host_program_eq, program, List.append_assoc]) (by rfl)

theorem labels_fresh_at_9 : LabelsFresh unmarshalSSZ 9 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_117 : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ 117 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_186 : LabelsFresh MemmoveGrowsliceModel 186 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_212 : LabelsFresh marshalSSZTo 212 := labelsFresh_of (by rw [host_program_eq]; decide)
theorem labels_fresh_at_180 : ∀ i < 180, Host.prog[i]? ≠ some (.label "runtime.makeslice") :=
  notLabel_of (by rw [host_program_eq]; decide)

theorem label_bump_pointer : label "runtime.modelBumpPointer" = 0x10000 :=
  mk_label program _ 0 _ (by simp [program, dataLabels]) (by simp [programLabels])

theorem label_write_barrier : label "runtime.writeBarrier" = 0x10008 :=
  mk_label program _ 8 _ (by simp [program, dataLabels]) (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev zero_word_bytes : List UInt8 := Int.toBytes 8 (0 : UInt64).toBitVec.toInt
abbrev pre : List UInt8 := [0xaa, 0xbb, 0xcc]

/-- bump pointer (→ 0x1000c) · writeBarrier · heap (32) · guard · input (40) · receiver (72)
· stack window: scratch (24) · rslot · m0 · m1 · m2 · g64 (16) · l30 · l28 · l20 · g24 · g16 · fp ·
return slot · spill rax · spill rbx · dst: prefix (3) · d0 (8) · d1 (32) · spare (5). -/
def block (e8 root : List UInt8) : List UInt8 :=
  Int.toBytes 8 (0x1000c : BitVec 64).toInt ++ ([0, 0, 0, 0] ++ (zeros 32 ++ (zero_word_bytes ++ (e8 ++ (root ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 32 ++ (zeros 24 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 16 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zero_word_bytes ++ (zeros 8 ++ (zeros 8 ++ (pre ++ (zeros 8 ++ (zeros 32 ++ zeros 5)))))))))))))))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def initial_state (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005c, 0x10034, 40, 0, 0, 0, 0x1011c, 0, 0, 0, 0, 0, 0, 0, 0x1001c, 0⟩, zmms, flags, mem e8 root⟩

theorem lift_heap {X : DataMem → Prop} {m : DataMem}
    (h : (Eq ((Int.toBytes 8 (0x1000c : BitVec 64).toInt).At (0x10000 : BitVec 64))
      ⋆ (Eq ((zeros 32).At (0x1000c : BitVec 64)) ⋆ X)) m) : (bumpHeap 32 ⋆ X) m := by
  rw [← Std.ExtHashMap.sep_assoc] at h
  exact sep_mono_left (fun m hm => ⟨0x1000c, by decide, by rw [label_bump_pointer]; exact hm⟩) h

set_option maxHeartbeats 16000000 in
/-- **Non-vacuity of `DecodeThenEncode.round_trip`.** Every premise holds in
this one host; the decoder returns nil; from the real middle memory (return
slot rewritten with `ra2 = 0`) the encoder returns `(0x10134, 3 + 40, 48, nil)`
and `dst[3..43]` = the 40 input bytes `e8 ++ root`. -/
theorem runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        Eventually (step1 Host.exe)
          (fun st' => st'.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st'.data.regs.rax = 0x10134
            ∧ st'.data.regs.rbx.toNat = (3 : UInt64).toNat + 40 ∧ st'.data.regs.rcx = 48
            ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0 ∧
            (Eq (pre.At (0x10134 : UInt64).toBitVec)
              ⋆ Eq ((e8 ++ root).At ((0x10134 : UInt64).toBitVec + (3 : UInt64).toBitVec))
              ⋆ Eq ((e8 ++ root).At (initial_state e8 root zmms flags).regs.rbx.toBitVec) ⋆ fun _ => True) st'.data.dmem)
          ⟨⟨{ st.data.regs with rax := (initial_state e8 root zmms flags).regs.rax, rbx := 0x10134, rcx := 3, rdi := 48, rsp := (initial_state e8 root zmms flags).regs.rsp },
              zmms, flags,
            st.data.dmem.storeInt (initial_state e8 root zmms flags).regs.rsp.toBitVec 8 (0 : UInt64).toBitVec.toInt⟩,
            Host.addrOf 212⟩)
      ⟨initial_state e8 root zmms flags, Host.addrOf 9⟩ :=
  eventually_mono (DecodeThenEncode.round_trip 9 placed_at_9 labels_fresh_at_9 117 placed_at_117 labels_fresh_at_117 212 placed_at_212 labels_fresh_at_212 e8 root he8 hroot
    (initial_state e8 root zmms flags) 0 0 0
    (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 32)
    (zeros 8) (zeros 8) (zeros 16) pre (zeros 8) (zeros 32)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    0x10134 3 48 rfl (by decide) (by decide)
    (Eq ((zeros 5).At (0x1015f : BitVec 64))) 24 (by omega) (by decide) (zeros 24) rfl
    bumpHeap 32
    (by
      have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
      witness_split [he8, hroot]
      rw [Std.ExtHashMap.sep_comm_l (Eq (([0, 0, 0, 0] : List UInt8).At _)) (Eq ((zeros 32).At _))] at H
      have H2 := lift_heap H
      simp only [initial_state, zero_word_bytes, label_write_barrier, UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat,
        BitVec.reduceAdd, BitVec.reduceSub] at H2 ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H2 ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H2 ⊢
      exact H2)
    (by simp [initial_state]) (by simp [initial_state]) rfl (by omega) (bump_makeslice1 180 placed_at_180 labels_fresh_at_180 _) (model_memmove 186 placed_at_186 labels_fresh_at_186 24)
    (model_memmove 186 placed_at_186 labels_fresh_at_186 _))
    (fun st h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2
      (st.data.dmem.storeInt (initial_state e8 root zmms flags).regs.rsp.toBitVec 8 (0 : UInt64).toBitVec.toInt) zmms flags
        (fun F hF => Mem.storeInt_sep _ 8 _ F _ ⟨hF, Int.toBytes_length 8 _⟩ _)⟩)

/-- epoch 0 / root 0; a representative value and pattern root; 2^64 − 1 and 0xff root. -/
example (z' : RegZmms) (f : StatusFlags) := runs (Int.toBytes 8 0) (zeros 32) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 0x0123456789abcdef) ((List.range 32).map (fun i => (UInt8.ofNat i))) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff) (by decide) rfl z' f

/-- Go-value element: the receiver of this witness (offset 0x5c of the block) is a zero `Checkpoint`
before the decoder; the receiver that the encoder reads is the decoder conclusion's fragments
`afterDecode` over it, a Go value for every `p ≠ 0`. Layout: `Prysm.Checkpoint.goFields`
(IR; trust note in `Prysm.Checkpoint.GoValue`). -/
theorem recv (p : BitVec 64) (hp : p ≠ 0) :
    goValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c) = true
    ∧ goValue (afterDecode (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c)
      (Int.toBytes 8 0x0123456789abcdef) p) = true :=
  have h : goValue (recvAt (block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c) = true := by
    decide
  ⟨h, after_decode_goValue _ _ h (by decide) p hp⟩

end Prysm.Checkpoint.Witness.DecodeThenEncode
