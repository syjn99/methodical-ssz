import Prysm.DataColumnsByRootIdentifier.EncodeFastPath
import Runtime.CopyModel
import Machine.WitnessHost

/-!
# Witnesses of `Encode.fast_path` (encoder fast path): n = 0, 1, 128

Host: the real Go 1.26.10 `(*v1alpha1.DataColumnsByRootIdentifier).MarshalSSZTo` (index 0) and `MemmoveGrowsliceModel` (index 118,
`model_memmove`, S = 0). One memory block at `0x10000`: guard word (r14 = 0xfff0), the receiver window (48 bytes:
`state` 0, BlockRoot = (0x10038, 32, cap 0), Columns = (pc, n, cap 0)), the 32 root bytes at 0x10038, the 168-byte
stack window from rsp − 144 (rsp = 0x100e8) to rsp + 24, `dst` at 0x10100 with len 0 and cap 36 + 8n (old contents
zero), and the 8n column bytes at pc = 0x10124 + 8n. Frame `R`: the receiver words the code does not read
(`state`, BlockRoot cap), the stack gaps at rsp − 136 (72 bytes), rsp − 48 and rsp − 16.
The root and column bytes are arbitrary lists of the right length; the `example`s instantiate them.
-/

open Machine Runtime Machine.Witness Prysm.DataColumnsByRootIdentifier.Code

namespace Prysm.DataColumnsByRootIdentifier.Witness.EncodeFastPath


def program : Program := marshalSSZTo ++ MemmoveGrowsliceModel

theorem program_length : program.length = 144 := by rfl

instance host : Host := mkHost program (by rw [program_length]; decide)

theorem placed_at_0 : marshalSSZTo.IsInfixAt Host.prog 0 := infixAt_of [] MemmoveGrowsliceModel (by simp [Host.prog, mkHost, program]) rfl
theorem placed_at_118 : MemmoveGrowsliceModel.IsInfixAt Host.prog 118 := infixAt_of marshalSSZTo [] (by simp [Host.prog, mkHost, program]) (by rfl)
theorem labels_fresh_at_0 : LabelsFresh marshalSSZTo 0 := fun i hi => absurd hi (Nat.not_lt_zero _)
theorem labels_fresh_at_118 : LabelsFresh MemmoveGrowsliceModel 118 := labelsFresh_of (by decide)

abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0
abbrev bitvec_word_bytes (v : BitVec 64) : List UInt8 := Int.toBytes 8 v.toInt

/-- guard · receiver (state, BlockRoot ptr/len/cap, Columns ptr/len) · root · rslot · gap 72 · l64 · l56 · gap ·
l40 · l32 · l24 · gap · fp · return address · spill rax · spill rbx · dst (36 + 8n) · columns. -/
def block (root cb : List UInt8) (pc nb : BitVec 64) (dl : Nat) : List UInt8 :=
  bitvec_word_bytes 0 ++ (zeros 8 ++ (bitvec_word_bytes 0x10038 ++ (Int.toBytes 8 32 ++ (zeros 8 ++ (bitvec_word_bytes pc ++ (bitvec_word_bytes nb ++ (root ++ (zeros 8 ++ (zeros 72 ++ (zeros 8
    ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (zeros 8 ++ (bitvec_word_bytes 0 ++ (zeros 8 ++ (zeros 8 ++ (zeros dl ++ cb)))))))))))))))))))))

def mem (root cb : List UInt8) (pc nb : BitVec 64) (dl : Nat) : DataMem :=
  (block root cb pc nb dl).At (0x10000 : BitVec 64)

def initial_state (root cb : List UInt8) (pc nb : BitVec 64) (dl : Nat) (zmms : RegZmms) (flags : StatusFlags) :
    MachineData :=
  ⟨⟨0x10008, 0x10100, 0, 0, 0, UInt64.ofNat dl, 0x100e8, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags,
    mem root cb pc nb dl⟩

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeFastPath`): 200000 and 1000000 fail (`whnf` timeout); 4000000 passes. Profile (the 1000000 build):
-- `simp` 12.3 s of the declaration, the `sep_comm` sort of the 26-chunk memory premise (the cause profiled for `Prysm.SyncAggregate.Witness.DecodeAccept.runs`).
set_option maxHeartbeats 4000000 in
/-- n = 0: `cap = 36 + 8n = 36`, Columns at 0x10124. -/
theorem runs_empty (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 0)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10100
        ∧ st.data.regs.rbx.toNat = 36 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x10124 0 36 zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 (initial_state root cb 0x10124 0 36 zmms flags) 0 0 0x10038 0x10124 0 0
    rfl (by decide) root cb [] (zeros 36) hroot (by rw [hcb]) rfl rfl (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl
    (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10020 : BitVec 64)) ⋆ Eq ((zeros 72).At (0x10060 : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x100b8 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100d8 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x10124 0 36).At (0x10000 : BitVec 64)) (mem root cb 0x10124 0 36) := rfl
      witness_split [hroot, hcb]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (model_memmove 118 placed_at_118 labels_fresh_at_118 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeFastPath`): 200000 and 1000000 fail (`whnf` timeout); 4000000 passes. Profile (the 1000000 build):
-- `simp` 12.3 s of the declaration, the `sep_comm` sort of the 26-chunk memory premise (the cause profiled for `Prysm.SyncAggregate.Witness.DecodeAccept.runs`).
set_option maxHeartbeats 4000000 in
/-- n = 1: `cap = 36 + 8n = 44`, Columns at 0x1012c. -/
theorem runs_one_element (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 8)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10100
        ∧ st.data.regs.rbx.toNat = 44 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x1012c 1 44 zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 (initial_state root cb 0x1012c 1 44 zmms flags) 0 0 0x10038 0x1012c 1 1
    rfl (by decide) root cb [] (zeros 44) hroot (by rw [hcb]) rfl rfl (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl
    (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10020 : BitVec 64)) ⋆ Eq ((zeros 72).At (0x10060 : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x100b8 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100d8 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x1012c 1 44).At (0x10000 : BitVec 64)) (mem root cb 0x1012c 1 44) := rfl
      witness_split [hroot, hcb]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (model_memmove 118 placed_at_118 labels_fresh_at_118 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

-- Measured (three builds of `Prysm.DataColumnsByRootIdentifier.WitnessEncodeFastPath`): 200000 and 1000000 fail (`whnf` timeout); 4000000 passes. Profile (the 1000000 build):
-- `simp` 12.3 s of the declaration, the `sep_comm` sort of the 26-chunk memory premise (the cause profiled for `Prysm.SyncAggregate.Witness.DecodeAccept.runs`).
set_option maxHeartbeats 4000000 in
-- maxRecDepth (builds at the default, 2000 and 20000, and a later run): 512 and 2000 fail; WitnessEncodeFastPath n = 128 passes at 4000, WitnessEncodeGrowFirstSite fails at 4000 and passes
-- at 8000 ("maximum recursion depth" at the declaration). Replacing `simp [initial_state]` by `dsimp only [initial_state]; decide`
-- did not remove it (one more run); the cause is not located. `runs_maximum` only (n = 0, 1 pass at the default).
set_option maxRecDepth 4000 in
/-- n = 128: `cap = 36 + 8n = 1060`, Columns at 0x10524. -/
theorem runs_maximum (root cb : List UInt8) (hroot : root.length = 32) (hcb : cb.length = 1024)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10100
        ∧ st.data.regs.rbx.toNat = 1060 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state root cb 0x10524 128 1060 zmms flags, Host.addrOf 0⟩ :=
  eventually_mono (Encode.fast_path 0 placed_at_0 labels_fresh_at_0 (initial_state root cb 0x10524 128 1060 zmms flags) 0 0 0x10038 0x10524 128 128
    rfl (by decide) root cb [] (zeros 1060) hroot (by rw [hcb]) rfl rfl (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 [] rfl
    (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10020 : BitVec 64)) ⋆ Eq ((zeros 72).At (0x10060 : BitVec 64))
      ⋆ Eq ((zeros 8).At (0x100b8 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x100d8 : BitVec 64)))
    (by
      have H : Eq ((block root cb 0x10524 128 1060).At (0x10000 : BitVec 64)) (mem root cb 0x10524 128 1060) := rfl
      witness_split [hroot, hcb]
      simp only [initial_state, bitvec_word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, UInt64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil,
        show (UInt64.ofNat 0).toBitVec = 0#64 from rfl] at H ⊢
      simp only [Std.ExtHashMap.sep_assoc] at H ⊢
      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢
      exact H)
    (by simp [initial_state]) (by simp [initial_state]) (model_memmove 118 placed_at_118 labels_fresh_at_118 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) := runs_empty (zeros 32) [] rfl rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_one_element ((List.range 32).map (fun i => UInt8.ofNat i)) (Int.toBytes 8 0x0123456789abcdef) (by decide) rfl z' f
example (z' : RegZmms) (f : StatusFlags) :=
  runs_maximum (List.replicate 32 0xff) (List.replicate 1024 0xff) (by decide) List.length_replicate z' f

end Prysm.DataColumnsByRootIdentifier.Witness.EncodeFastPath
