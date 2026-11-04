module
public import Kraken.X64.Parser
public import Fk.Include
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

/-! Both Kraken parsers agree where the elaborator accepts the file. -/
example : FixedVecSizeSSZ = include_x64 "../link/out/norm/target.FixedVec.SizeSSZ.S" := by decide
example : ListU64SizeSSZ = include_x64 "../link/out/norm/target.ListU64.SizeSSZ.S" := by decide
example : ScalarsMarshalSSZTo = include_x64 "../link/out/norm/target.Scalars.MarshalSSZTo.S" := by decide
example : ScalarsSizeSSZ = include_x64 "../link/out/norm/target.Scalars.SizeSSZ.S" := by decide
example : ScalarsUnmarshalSSZ = include_x64 "../link/out/norm/target.Scalars.UnmarshalSSZ.S" := by decide
end Fk.Code
