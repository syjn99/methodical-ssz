module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `v1alpha1.Deposit`

This module holds the program constant `Code.unmarshalSSZ` of `v1alpha1.Deposit`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.Deposit

/-- `(*v1alpha1.Deposit).UnmarshalSSZ` (protoc type, `phase0.ssz.go:2059`). -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ.S"

end Prysm.Deposit
