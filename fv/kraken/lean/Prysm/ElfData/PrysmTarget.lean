import Kraken.X64.WP
import Runtime.StaticUint64s
import Machine.Include

/-!
# ELF data of the Prysm target that the theorems read

Every definition below is elaborated by `data_include` (`Machine/Include.lean`) from a file of `fv/kraken/prysm/go1.26.10/link-set/data/`.
`gen/checks/link_set.py` writes the files from the item table `prysm/go1.26.10/link-set.tsv` and the operands of the
converted code. The data check of `link/check.py` compares them with the ELF
(`prysm/go1.26.10/link-set/RESULT`). No byte and no offset below is written by hand.
The names keep the ids of the data files. An operand that two functions share has one data file.
The address lemmas at the end give the label form of some addresses. `rfl` proves each of them.
The table `runtime.staticuint64s` of the same directory is `Runtime.Data.staticuint64s` (`Runtime/StaticUint64s.lean`).
-/

namespace ElfData.PrysmTarget

-- Checkpoint and Epoch
-- the uint8 element type word (makeslice in the decoder, growslice in the encoder)
data_include typeUint8
-- "Epoch: %w" (Checkpoint decoder, error path) and its errors.errorString type
data_include formatEpoch
data_include typeErrorString
data_include itabErrorStringError
-- error globals: addresses only (values are set by the runtime's package init)
data_include sszErrSize
data_include sszErrBytesLength
-- Epoch decoder reject: format, type:int, the static box of the constant 8
data_include formatBufferLength
data_include typeInt
data_include boxedEight

-- AttestationData
-- the Checkpoint abi.Type word passed to runtime.newobject (decoder Source/Target, encoder nil fields)
data_include typeCheckpoint
-- the four field wraps "Slot: %w", "CommitteeIndex: %w", "Source: %w", "Target: %w"
data_include formatSlot
data_include formatCommitteeIndex
data_include formatSource
data_include formatTarget

-- IndexedAttestation
-- element type word of `make([]uint64, numElem)` (makeslice esz 8): abi.Type of uint64 (Size_ 8, Kind 11)
data_include typeUint64
-- type word of `new(AttestationData)` (newobject sz 96): abi.Type of the struct (Size_ 96, Kind 25)
data_include typeAttestationData
-- the two `fmt.Errorf` formats of the list rejects ("%d … %w")
data_include formatAttestingIndicesTooBig
data_include formatAttestingIndicesMisaligned
-- error globals: addresses only (values are set by the runtime's package init)
data_include sszErrListTooBig
data_include sszErrIncorrectListSize
data_include sszErrInvalidVariableOffset

-- SyncAggregate and SyncCommittee
-- the element type word of the SyncCommittee `[][]byte` backing array (`make([][]byte, 512)`,
-- makeslice esz 24): abi.Type of `[]uint8`
data_include typeUint8Slice

-- DataColumnsByRootIdentifier decoder
-- "ssz-max exceeded: c.Columns has %d elements, ssz-max is 128: %w" (63 bytes)
data_include formatColumnsTooBig
-- "misaligned bytes: c.Columns length is %d, which is not a multiple of 8: %w" (74 bytes)
data_include formatColumnsMisaligned

-- Deposit decoder: the type descriptor of `v1alpha1.Deposit_Data` (newobject of 120 bytes)
data_include typeDeposit_Data

-- The address lemmas. `variable [Host]` comes after the data includes, so it binds only these lemmas.
variable [Host]

theorem sszErrSize_addr_eq : ElfData.PrysmTarget.sszErrSize_addr = (label "ssz.ErrSize").toBitVec := rfl
theorem sszErrBytesLength_addr_eq : ElfData.PrysmTarget.sszErrBytesLength_addr = (label "ssz.ErrBytesLength").toBitVec := rfl
theorem sszErrIncorrectListSize_addr_eq : ElfData.PrysmTarget.sszErrIncorrectListSize_addr = (label "ssz.ErrIncorrectListSize").toBitVec := rfl
theorem sszErrListTooBig_addr_eq : ElfData.PrysmTarget.sszErrListTooBig_addr = (label "ssz.ErrListTooBig").toBitVec := rfl
theorem formatAttestingIndicesMisaligned_addr_eq : ElfData.PrysmTarget.formatAttestingIndicesMisaligned_addr = (label "go_string._" + 171660).toBitVec := rfl
theorem formatAttestingIndicesTooBig_addr_eq : ElfData.PrysmTarget.formatAttestingIndicesTooBig_addr = (label "go_string._" + 164102).toBitVec := rfl
theorem typeInt_addr_eq : ElfData.PrysmTarget.typeInt_addr = (label "type__" + 387520).toBitVec := rfl

end ElfData.PrysmTarget
