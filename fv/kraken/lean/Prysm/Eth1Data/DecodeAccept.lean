import Prysm.Eth1Data.DecodeAddressArithmetic
import Prysm.Eth1Data.GeneratedDecodeAccept

/-!
# The name `Prysm.Eth1Data.Decode.accept`

The accept theorem of the real `(*v1alpha1.Eth1Data).UnmarshalSSZ` is the generated theorem
`Decode.generated_accept` (`Prysm/Eth1Data/GeneratedDecodeAccept.lean`, `decoder --whole-accept`).
`Decode.accept` is that theorem under a second name. Its proof is the generated proof term, not a second proof.
The name stays for two users:
- the generator test fixture `Prysm/Eth1Data/GeneratedDecodeAcceptComposition.lean` (`decoder --field-segments --compose
  --same-as Prysm.Eth1Data.Decode.accept`), which `gen/generator/decoder_test.py` compares with the generator output;
- `gen/tools/proof_inventory.py`, which takes `Decode.accept` before `Decode.generated_accept` as the accept theorem.
-/

open Machine Runtime

namespace Prysm.Eth1Data

/-- **Accept path of the real `(*v1alpha1.Eth1Data).UnmarshalSSZ` (Go 1.26.10)**: the generated theorem
`Decode.generated_accept`. On a 72-byte input the decoder returns nil, and the receiver holds fresh 32-byte
DepositRoot = buf[0:32] and BlockHash = buf[40:72] (len = cap = 32 each) and DepositCount = buf[32:40]. -/
theorem Decode.accept : type_of% @Decode.generated_accept := @Decode.generated_accept

end Prysm.Eth1Data
