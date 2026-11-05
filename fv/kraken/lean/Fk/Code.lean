module
public import Kraken.X64.Parser
public import Fk.Include
public import Fk.SHash
@[expose] public section
namespace Fk.Code
def FixedVecMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.FixedVec.MarshalSSZTo.S"
def FixedVecSizeSSZ : Program := include_x64_rt "../link/out/norm/target.FixedVec.SizeSSZ.S"
def FixedVecUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.FixedVec.UnmarshalSSZ.S"
def ListU64MarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.ListU64.MarshalSSZTo.S"
def ListU64SizeSSZ : Program := include_x64_rt "../link/out/norm/target.ListU64.SizeSSZ.S"
def ListU64UnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.ListU64.UnmarshalSSZ.S"
def ScalarsMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.Scalars.MarshalSSZTo.S"
def ScalarsSizeSSZ : Program := include_x64_rt "../link/out/norm/target.Scalars.SizeSSZ.S"
def ScalarsUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.Scalars.UnmarshalSSZ.S"

def BitLMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.BitL.MarshalSSZTo.S"
def BitLSizeSSZ : Program := include_x64_rt "../link/out/norm/target.BitL.SizeSSZ.S"
def BitLUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.BitL.UnmarshalSSZ.S"
def BitVecMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.BitVec.MarshalSSZTo.S"
def BitVecSizeSSZ : Program := include_x64_rt "../link/out/norm/target.BitVec.SizeSSZ.S"
def BitVecUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.BitVec.UnmarshalSSZ.S"
def ListCMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.ListC.MarshalSSZTo.S"
def ListCSizeSSZ : Program := include_x64_rt "../link/out/norm/target.ListC.SizeSSZ.S"
def ListCUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.ListC.UnmarshalSSZ.S"
def NestedMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target.Nested.MarshalSSZTo.S"
def NestedSizeSSZ : Program := include_x64_rt "../link/out/norm/target.Nested.SizeSSZ.S"
def NestedUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target.Nested.UnmarshalSSZ.S"
def PrysmAttestationDataMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target_prysm.AttestationData.MarshalSSZTo.S"
def PrysmAttestationDataSizeSSZ : Program := include_x64_rt "../link/out/norm/target_prysm.AttestationData.SizeSSZ.S"
def PrysmAttestationDataUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target_prysm.AttestationData.UnmarshalSSZ.S"
def PrysmCheckpointMarshalSSZTo : Program := include_x64_rt "../link/out/norm/target_prysm.Checkpoint.MarshalSSZTo.S"
def PrysmCheckpointSizeSSZ : Program := include_x64_rt "../link/out/norm/target_prysm.Checkpoint.SizeSSZ.S"
def PrysmCheckpointUnmarshalSSZ : Program := include_x64_rt "../link/out/norm/target_prysm.Checkpoint.UnmarshalSSZ.S"
-- ssz.ValidateBitlist is not included: Kraken does not parse `bsr` (REPORT-1b, Kraken requests).

/-! Both Kraken parsers agree where the elaborator accepts the file. -/
example : FixedVecSizeSSZ = include_x64 "../link/out/norm/target.FixedVec.SizeSSZ.S" := by decide
example : ListU64SizeSSZ = include_x64 "../link/out/norm/target.ListU64.SizeSSZ.S" := by decide
example : ScalarsMarshalSSZTo = include_x64 "../link/out/norm/target.Scalars.MarshalSSZTo.S" := by decide
example : ScalarsSizeSSZ = include_x64 "../link/out/norm/target.Scalars.SizeSSZ.S" := by decide
example : ScalarsUnmarshalSSZ = include_x64 "../link/out/norm/target.Scalars.UnmarshalSSZ.S" := by decide
end Fk.Code
