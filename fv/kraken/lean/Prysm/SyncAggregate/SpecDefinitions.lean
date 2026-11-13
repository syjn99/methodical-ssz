import Runtime.Contracts
import Prysm.Checkpoint.Spec
import Prysm.SyncAggregate.SpecDescription

/-!
# Definitions that the SyncAggregate and SyncCommittee statements use: the `SyncAggregate` part

The declarations of the other types of this group are in `Prysm/SyncCommittee/SpecDefinitions.lean`.
-/

open Machine Runtime EthLib.Serialization.Ssz

namespace Prysm.SyncAggregate

/-- SSZ content of a Go `v1alpha1.SyncAggregate` (SyncCommitteeBits 64 bytes, SyncCommitteeSignature 96). -/
structure SszValue where
  bits : Vector UInt8 64
  signature : Vector UInt8 96

/-- Bitvector[512] is the 512 bits of the 64 bytes, lowest bit of byte 0 first (EthLib `unpackBits`). -/
def SszValue.toValue (g : Prysm.SyncAggregate.SszValue) : Value :=
  .seq [.bits (unpackBits g.bits.toArray 512), .bytes g.signature.toArray]

/-- `bits ‖ signature`. -/
def SszValue.encode (g : Prysm.SyncAggregate.SszValue) : Array UInt8 := g.bits.toArray ++ g.signature.toArray

end Prysm.SyncAggregate
