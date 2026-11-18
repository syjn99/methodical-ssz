import Prysm.RuntimeModel.BumpAllocatorUint64AndStructDispatch
import Prysm.RuntimeModel.BumpAllocatorByteSliceDispatch

/-! Hand list of the declarations of `Prysm/RuntimeModel/` for `gen/checks/axioms_gate.py`.
Each name must be in the declaration dump and use only the standard axioms. -/

#print axioms Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size1
#print axioms Prysm.RuntimeModel.bump_makeslice_uint64_dispatch_size8
#print axioms Prysm.RuntimeModel.bump_newobject_struct_dispatch_size72
#print axioms Prysm.RuntimeModel.bump_newobject_struct_dispatch_size96
#print axioms Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size1
#print axioms Prysm.RuntimeModel.bump_makeslice_byte_slice_dispatch_size24
