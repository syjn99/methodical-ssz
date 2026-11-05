# Functions in the ELF (B3.0): instructions, calls, globals

GOAMD64=v1. Kraken runtime parser (after link/conv.py --norm): every function parses except ssz.ValidateBitlist (1 line: `bsr %r8d,%r8d`).

| function | instructions | calls | globals |
| --- | --- | --- | --- |
| ssz.ValidateBitlist | 133 | fmt.errorf convT64 morestack_noctxt.abi0 newobject  |  |
| target_prysm.AttestationData.MarshalSSZTo | 307 | fmt.errorf gcWriteBarrier2 growslice memmove morestack_noctxt.abi0 newobject  | runtime.writeBarrier ssz.ErrBytesLength  |
| target_prysm.AttestationData.SizeSSZ | 2 |  |  |
| target_prysm.AttestationData.UnmarshalSSZ | 169 | gcWriteBarrier2 makeslice memmove morestack_noctxt.abi0 newobject  | runtime.writeBarrier ssz.ErrSize  |
| target_prysm.Checkpoint.MarshalSSZTo | 76 | growslice memmove morestack_noctxt.abi0  | ssz.ErrBytesLength  |
| target_prysm.Checkpoint.SizeSSZ | 2 |  |  |
| target_prysm.Checkpoint.UnmarshalSSZ | 65 | gcWriteBarrier2 makeslice memmove morestack_noctxt.abi0  | runtime.writeBarrier ssz.ErrSize  |
| target.BitL.MarshalSSZTo | 79 | growslice memmove morestack_noctxt.abi0  | ssz.ErrListTooBig  |
| target.BitL.SizeSSZ | 3 |  |  |
| target.BitL.UnmarshalSSZ | 124 | fmt.errorf gcWriteBarrier2 growslice memmove morestack_noctxt.abi0 newobject ssz.ValidateBitlist  | runtime.writeBarrier ssz.ErrInvalidVariableOffset ssz.ErrSize  |
| target.BitVec.MarshalSSZTo | 54 | growslice morestack_noctxt.abi0  | ssz.ErrBytesLength  |
| target.BitVec.SizeSSZ | 2 |  |  |
| target.BitVec.UnmarshalSSZ | 58 | gcWriteBarrier2 makeslice morestack_noctxt.abi0  | runtime.writeBarrier ssz.ErrSize  |
| target.FixedVec.MarshalSSZTo | 91 | growslice memmove morestack_noctxt.abi0  | ssz.ErrBytesLength  |
| target.FixedVec.SizeSSZ | 2 |  |  |
| target.FixedVec.UnmarshalSSZ | 75 | gcWriteBarrier2 makeslice memmove morestack_noctxt.abi0 panicBounds  | runtime.writeBarrier ssz.ErrSize  |
| target.ListC.MarshalSSZTo | 213 | fmt.errorf growslice morestack_noctxt.abi0 newobject  | ssz.ErrListTooBig  |
| target.ListC.SizeSSZ | 14 |  |  |
| target.ListC.UnmarshalSSZ | 395 | fmt.errorf convT64 gcWriteBarrier1 gcWriteBarrier2 makeslice morestack_noctxt.abi0 newobject panicBounds target.ListU64.UnmarshalSSZ  | runtime.writeBarrier ssz.ErrInvalidVariableOffset ssz.ErrListTooBig ssz.ErrSize  |
| target.ListU64.MarshalSSZTo | 83 | growslice morestack_noctxt.abi0  | ssz.ErrListTooBig  |
| target.ListU64.SizeSSZ | 4 |  |  |
| target.ListU64.UnmarshalSSZ | 175 | fmt.errorf convT64 gcWriteBarrier2 makeslice morestack_noctxt.abi0 newobject panicBounds  | runtime.writeBarrier ssz.ErrIncorrectListSize ssz.ErrInvalidVariableOffset ssz.ErrListTooBig ssz.ErrSize  |
| target.Nested.MarshalSSZTo | 298 | fmt.errorf gcWriteBarrier2 growslice morestack_noctxt.abi0 newobject  | runtime.writeBarrier ssz.ErrListTooBig  |
| target.Nested.SizeSSZ | 33 | gcWriteBarrier2 morestack_noctxt.abi0 newobject  | runtime.writeBarrier  |
| target.Nested.UnmarshalSSZ | 142 | fmt.errorf gcWriteBarrier2 morestack_noctxt.abi0 newobject target.ListU64.UnmarshalSSZ target.Scalars.UnmarshalSSZ  | runtime.writeBarrier ssz.ErrInvalidVariableOffset ssz.ErrSize  |
| target.Scalars.MarshalSSZTo | 122 | growslice morestack_noctxt.abi0  |  |
| target.Scalars.SizeSSZ | 2 |  |  |
| target.Scalars.UnmarshalSSZ | 28 |  | ssz.ErrInvalidSerialization ssz.ErrSize  |
