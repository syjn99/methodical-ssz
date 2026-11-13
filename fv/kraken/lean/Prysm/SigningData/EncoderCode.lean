import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the encoder of `v1alpha1.SigningData` (Go 1.26.10 ELF `c6403c02…911e`)

The constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/enc2/link/norm`.
The link check, the bundle hash and the rebuild limit are in `Prysm/BlobIdentifier/EncoderCode.lean`, which imports this module.
-/

namespace Prysm.SigningData

/-- `(*v1alpha1.SigningData).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_rt "../prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo.S"

end Prysm.SigningData
