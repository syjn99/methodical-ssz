import Runtime.Contracts
import Machine.Frame
import Machine.Bytes
import Codec.Bytes32Decode
import Prysm.Eth1Data.Code

/-!
# Address and stack arithmetic of the decoders with the frame `sub $0x20`

Hand-written. No theorem about Eth1Data machine code is here.
Hand accept proofs of other decoders with the same frame use these two declarations.
- `eth1_data_addr`: closes an address equation by `toNat` and `omega`.
- `Decode.stack_low_eq`: the two forms of the address of the runtime callees' stack bytes.
-/

open Machine Runtime

namespace Prysm.Eth1Data

/-- Address equation by `toNat` and `omega` (as `beacon_block_header_addr`). -/
macro "eth1_data_addr" : tactic => `(tactic| (
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat,
    UInt64.toNat_toBitVec, UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow]
  all_goals omega))

theorem Decode.stack_low_eq (x : BitVec 64) (S : Nat) : x - 40 - 8 - BitVec.ofNat 64 S = x - 48 - BitVec.ofNat 64 S := by
  bv_omega

end Prysm.Eth1Data
