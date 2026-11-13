import Runtime.Contracts
import Prysm.Checkpoint.Spec
import Prysm.SyncAggregate.SpecDescription
import Prysm.SyncAggregate.SpecDefinitions
import Codec.ByteSliceListDefinitions

/-!
# Definitions that the SyncAggregate and SyncCommittee statements use

These definitions are part of the frozen statements (`Prysm/SyncAggregate/Statements.lean`, `Prysm/SyncCommittee/Statements.lean`). A later change needs a
new name and a reason; the original stays.

- The statements also use `Codec.elementBlocks` and `Codec.sliceHeaders` (`Codec/ByteSliceListDefinitions.lean`):
  the element blocks of a slice of byte slices, and the backing array of its slice headers.
- `Prysm.SyncAggregate.SszValue`, `SszValue`: the SSZ content of a Go `v1alpha1.SyncAggregate` / `v1alpha1.SyncCommittee` whose byte
  fields have the lengths of the spec (64 / 96; 512 × 48 / 48). `toValue` is the EthLib `Value`,
  `Prysm.SyncAggregate.SszValue.encode` / `SszValue.encode` the 160 / 24624 bytes of the SSZ encoding (fixed-size container: the fields in order).
After the split of this module, the declarations of the other types are in `Prysm/SyncAggregate/SpecDefinitions.lean`.
-/

open Machine Runtime EthLib.Serialization.Ssz

namespace Prysm.SyncCommittee

/-- SSZ content of a Go `v1alpha1.SyncCommittee` (512 Pubkeys of 48 bytes, AggregatePubkey 48). -/
structure SszValue where
  pubkeys : Vector (Vector UInt8 48) 512
  aggregatePubkey : Vector UInt8 48

/-- The 512 pubkeys as byte lists, in order. -/
def SszValue.pks (g : SszValue) : List (List UInt8) := g.pubkeys.toList.map (·.toList)

def SszValue.toValue (g : SszValue) : Value :=
  .seq [.seq (g.pubkeys.toList.map fun p => .bytes p.toArray), .bytes g.aggregatePubkey.toArray]

/-- `pubkeys[0] ‖ … ‖ pubkeys[511] ‖ aggregatePubkey`. -/
def SszValue.encode (g : SszValue) : Array UInt8 := g.pks.flatten.toArray ++ g.aggregatePubkey.toArray

end Prysm.SyncCommittee
