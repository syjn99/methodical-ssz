import Runtime.Contracts
import Machine.Frame
import Machine.Bytes

/-!
# Address and stack arithmetic of the decoders with the frame `sub $0x60`

Hand-written. No theorem about BeaconBlockHeader machine code is here.
The hand proofs of the SyncCommitteeMessage decoder (the same frame) use these declarations.
- `beacon_block_header_addr`: closes an address equation by `toNat` and `omega`.
- `Decode.accept_guard`: the stack guard below the callee return slot.
- `Decode.head_stack_pointer`: rsp after the prologue.
- `Decode.low_stack_split`, `Decode.stack_low_eq`: the two forms of the address of the runtime callees' stack bytes.
- `Decode.split_three_words`: the 24-byte argument area as three 8-byte words.

Each theorem has the section binder `[Host]`, as the hand decoder lemmas of the other types.
-/

open Machine Runtime
variable [Host]

namespace Prysm.BeaconBlockHeader

theorem Decode.accept_guard (x : BitVec 64) (g : Nat) (h : g + 112 < x.toNat) : g < (x - 112).toNat := by bv_omega

theorem Decode.head_stack_pointer (x : BitVec 64) : x - 8#64 - 96 = x - 104 := by bv_omega

/-- Address equation by `toNat` and `omega` (as `address_equation`, with `Width.bits` reduced). -/
macro "beacon_block_header_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

theorem Decode.low_stack_split (x : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S) (hf : f.length = 8) :
    Eq ((a ++ f).At (x - 120 - BitVec.ofNat 64 S)) = Eq (a.At (x - 120 - BitVec.ofNat 64 S)) ⋆ Eq (f.At (x - 120)) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]; bv_omega

theorem Decode.stack_low_eq (x : BitVec 64) (S : Nat) : x - 104 - 8 - BitVec.ofNat 64 (S + 8) = x - 120 - BitVec.ofNat 64 S := by
  have : BitVec.ofNat 64 (S + 8) = BitVec.ofNat 64 S + 8 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

theorem Decode.split_three_words (x : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8) :
    Eq ((a ++ (b ++ c)).At (x - 104)) = Eq (a.At (x - 104)) ⋆ Eq (b.At (x - 96)) ⋆ Eq (c.At (x - 88)) := by
  rw [at_app _ _ (b := x - 96) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x - 88) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

end Prysm.BeaconBlockHeader
