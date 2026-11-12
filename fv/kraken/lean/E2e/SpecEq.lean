import E2e.Spec

/-!
# The hand Desc and the checker Desc have the same codec

`prysmCpDesc` (consensus-specs names `epoch`, `root`) and the Desc checker's
`cpCheckerDesc` (Go names `Epoch`, `Root`) differ only in the field names.
EthLib's `serialize` and `deserialize` ignore the names of a container
(`| .container _ fields, …`), so the two Descs encode and decode every value and
every byte array the same way. With `prysmCpDesc_checker` this is the equality
of the spec bridge, stated on the codec.
-/

namespace E2e
open EthLib.Serialization.Ssz

theorem prysmCpDesc_serialize_checker (v : Value) : serialize prysmCpDesc v = serialize cpCheckerDesc v := by
  unfold prysmCpDesc cpCheckerDesc
  cases v <;> simp only [serialize]

theorem prysmCpDesc_deserialize_checker (bs : Bytes) : deserialize prysmCpDesc bs = deserialize cpCheckerDesc bs := by
  unfold prysmCpDesc cpCheckerDesc
  simp only [deserialize]

end E2e
