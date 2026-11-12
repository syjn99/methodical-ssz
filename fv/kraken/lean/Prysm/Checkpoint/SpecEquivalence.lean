import Prysm.Checkpoint.Spec

/-!
# The hand Desc and the checker Desc have the same codec

`desc` (consensus-specs names `epoch`, `root`) and the Desc checker's
`checkerDesc` (Go names `Epoch`, `Root`) differ only in the field names.
EthLib's `serialize` and `deserialize` ignore the names of a container
(`| .container _ fields, …`), so the two Descs encode and decode every value and
every byte array the same way. With `desc_checker` this is the equality
of the spec bridge, stated on the codec.
-/

namespace Prysm.Checkpoint
open EthLib.Serialization.Ssz

theorem desc_serialize_checker (v : Value) : serialize desc v = serialize checkerDesc v := by
  unfold desc checkerDesc
  cases v <;> simp only [serialize]

theorem desc_deserialize_checker (bs : Bytes) : deserialize desc bs = deserialize checkerDesc bs := by
  unfold desc checkerDesc
  simp only [deserialize]

end Prysm.Checkpoint
