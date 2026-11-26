module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `v1.DepositRequest`

This module holds the program constants `Code.unmarshalSSZ` and `Code.marshalSSZTo` of `v1.DepositRequest`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.DepositRequest

/-- `(*v1.DepositRequest).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ.S"
/-- `(*v1.DepositRequest).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo.S"

end Prysm.DepositRequest
