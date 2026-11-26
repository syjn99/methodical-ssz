module

public import Kraken.X64.Parser
public import Machine.Include

@[expose] public section

/-!
# Code of `v1alpha1.VoluntaryExit`

This module holds the program constants `Code.unmarshalSSZ` and `Code.marshalSSZTo` of `v1alpha1.VoluntaryExit`.
Each program constant includes a `.S` file of the link set `prysm/go1.26.10/link-set/norm`.
The link set comes from the ELF of `prysm/go1.26.10/build-ids.txt`.
This file is written by hand.
-/

namespace Prysm.VoluntaryExit

/-- `(*v1alpha1.VoluntaryExit).UnmarshalSSZ`. -/
def Code.unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ.S"

/-- `(*v1alpha1.VoluntaryExit).MarshalSSZTo`. -/
def Code.marshalSSZTo : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo.S"

end Prysm.VoluntaryExit
