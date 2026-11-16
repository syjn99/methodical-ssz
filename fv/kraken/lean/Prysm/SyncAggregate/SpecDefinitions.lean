import Runtime.Contracts
import Prysm.Checkpoint.Spec
import Prysm.SyncAggregate.SpecDescription

/-!
# Definitions that the SyncAggregate statements use

These definitions are part of the statements of `Prysm/SyncAggregate/Statements.lean`.

- `SszValue`: the SSZ content of a Go `v1alpha1.SyncAggregate` whose byte fields have the lengths of the spec (64, 96).
- `SszValue.toValue` is the EthLib `Value`.
- `SszValue.encode` gives the 160 bytes of the SSZ encoding (fixed-size container: the fields in order).
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
