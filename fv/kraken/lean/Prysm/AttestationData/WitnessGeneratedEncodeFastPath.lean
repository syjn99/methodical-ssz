import Prysm.AttestationData.GeneratedEncodeFastPath
import Prysm.AttestationData.WitnessEncodeFastPath

/-!
# Witness of `Encode.generated_fast` (generated encoder fast path)

The witness uses the host, the placements and the memory blocks of `WitnessEncodeFastPath.lean`.
The host has `MemmoveGrowsliceModel` at index 0 (`model_memmove`, S = 0).
It has the Go 1.26.10 `(*v1alpha1.Checkpoint).MarshalSSZTo` at index 26 and `(*v1alpha1.AttestationData).MarshalSSZTo` at index 117.
`runs_empty` has an empty prefix and `cap = 128`.
`runs_prefix` has the prefix `[0xaa, 0xbb, 0xcc]` and `cap = 131`.
The memory premise of `Encode.generated_fast` is the memory premise of the hand witness in another chunk order.
A person writes this file, because `gen/flat-types/flat_types_encode_spec.py` has no form for a nested field.
-/

open Machine Runtime Machine.Witness Prysm.AttestationData.Witness.EncodeFastPath

namespace Prysm.AttestationData.Witness.GeneratedEncodeFastPath

/-- **Non-vacuity of `Encode.generated_fast`.** -/
theorem runs_empty (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10288
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨initial_state sl ix root e1 root1 e2 root2 zmms flags, Host.addrOf 117⟩ :=
  eventually_mono (Encode.generated_fast 117 placed_code fresh_code 26 placed_checkpoint fresh_checkpoint
    sl ix root e1 root1 e2 root2 (zeros 8) (word_bytes 32) (zeros 32) (zeros 8) (word_bytes 32) (zeros 32) []
    (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32)
    hsl hix hroot he1 hroot1 he2 hroot2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    0x10048 0x10068 0x100b0 0x100d0 0x10118 (by decide) (by decide) (initial_state sl ix root e1 root1 e2 root2 zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10030 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x101b8 : BitVec 64))
      ⋆ Eq ((zeros 40).At (0x101c8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10248 : BitVec 64))) 0 (by decide) (zeros 120) rfl
    (cast (congrFun (by ac_rfl) _) (mem_premise sl ix root e1 root1 e2 root2 hsl hix hroot he1 hroot1 he2 hroot2 zmms flags))
    (by simp [initial_state]) (by simp [initial_state]) (by simp [initial_state]) (model_memmove 0 placed_model fresh_model 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_empty (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (Int.toBytes 8 1) (List.replicate 32 0xaa) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff)
    (by decide) (by decide) rfl (by decide) rfl (by decide) rfl z' f

/-- **Non-vacuity of `Encode.generated_fast` with a prefix.** -/
theorem runs_prefix (sl ix root e1 root1 e2 root2 : List UInt8) (hsl : sl.length = 8) (hix : ix.length = 8)
    (hroot : root.length = 32) (he1 : e1.length = 8) (hroot1 : root1.length = 32) (he2 : e2.length = 8)
    (hroot2 : root2.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x10288
        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)
      ⟨Prefix.initial_state sl ix root e1 root1 e2 root2 zmms flags, Host.addrOf 117⟩ :=
  eventually_mono (Encode.generated_fast 117 placed_code fresh_code 26 placed_checkpoint fresh_checkpoint
    sl ix root e1 root1 e2 root2 (zeros 8) (word_bytes 32) (zeros 32) (zeros 8) (word_bytes 32) (zeros 32) [0xaa, 0xbb, 0xcc]
    (zeros 8) (zeros 8) (zeros 32) (zeros 8) (zeros 32) (zeros 8) (zeros 32)
    hsl hix hroot he1 hroot1 he2 hroot2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    0x10048 0x10068 0x100b0 0x100d0 0x10118 (by decide) (by decide) (Prefix.initial_state sl ix root e1 root1 e2 root2 zmms flags) 0 0 rfl
    (zeros 8) (zeros 8) (zeros 8) (zeros 16) (zeros 16) (zeros 16) (zeros 16) (zeros 8) (zeros 8) (zeros 8) (zeros 8)
    (zeros 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Eq ((zeros 8).At (0x10008 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x10030 : BitVec 64)) ⋆ Eq ((zeros 8).At (0x101b8 : BitVec 64))
      ⋆ Eq ((zeros 40).At (0x101c8 : BitVec 64)) ⋆ Eq ((zeros 32).At (0x10248 : BitVec 64))) 0 (by decide) (zeros 120) rfl
    (cast (congrFun (by ac_rfl) _) (Prefix.mem_premise sl ix root e1 root1 e2 root2 hsl hix hroot he1 hroot1 he2 hroot2 zmms flags))
    (by simp [Prefix.initial_state]) (by simp [Prefix.initial_state]) (by simp [Prefix.initial_state]) (model_memmove 0 placed_model fresh_model 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)

example (z' : RegZmms) (f : StatusFlags) :=
  runs_prefix (Int.toBytes 8 0x0123456789abcdef) (Int.toBytes 8 7) ((List.range 32).map (fun i => (UInt8.ofNat i)))
    (Int.toBytes 8 1) (List.replicate 32 0xaa) (Int.toBytes 8 (2 ^ 64 - 1)) (List.replicate 32 0xff)
    (by decide) (by decide) rfl (by decide) rfl (by decide) rfl z' f

end Prysm.AttestationData.Witness.GeneratedEncodeFastPath
