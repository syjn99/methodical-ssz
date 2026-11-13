import Kraken.X64.WP
import Runtime.StaticUint64s
import Prysm.ElfData.PrysmTargetReader

/-!
# ELF data of the Prysm target that the theorems read

Every definition below is elaborated by `prysm_data_include` from a file of `fv/kraken/prysm/go1.26.10/link-set/data/`.
`gen/e2e/link_set.py data` writes the files with the item tables of the `gen/e2e/*link.py` scripts and
`link/data.py`'s code, from the operands of the converted code. `link/check.py` (f) compares them with the ELF
(`prysm/go1.26.10/link-set/RESULT`). No byte and no offset below is written by hand.
The names keep the ids of the data files. An operand that two functions share has one data file.
The address lemmas at the end give the label form of some addresses. `rfl` proves each of them.
-/

namespace ElfData.PrysmTarget

-- Checkpoint and Epoch
-- the uint8 element type word (makeslice in the decoder, growslice in the encoder)
prysm_data_include e2eU8Type
-- "Epoch: %w" (Checkpoint decoder, error path) and its errors.errorString type
prysm_data_include e2eCpFmtW
prysm_data_include e2eErrStrType
prysm_data_include e2eErrorStringItab
-- error globals: addresses only (values are set by the runtime's package init)
prysm_data_include e2eErrSize
prysm_data_include e2eErrBytesLength
-- Epoch decoder reject: format, type:int, the static box of the constant 8, staticuint64s
prysm_data_include e2eEpFmt
prysm_data_include e2eIntType
prysm_data_include e2eEight
prysm_data_include e2eStaticuint64s

-- AttestationData
-- the Checkpoint abi.Type word passed to runtime.newobject (decoder Source/Target, encoder nil fields)
prysm_data_include adCpType
-- the four field wraps "Slot: %w", "CommitteeIndex: %w", "Source: %w", "Target: %w"
prysm_data_include adFmtSlot
prysm_data_include adFmtCi
prysm_data_include adFmtSource
prysm_data_include adFmtTarget

-- IndexedAttestation
-- element type word of `make([]uint64, numElem)` (makeslice esz 8): abi.Type of uint64 (Size_ 8, Kind 11)
prysm_data_include lvU64Type
-- type word of `new(AttestationData)` (newobject sz 96): abi.Type of the struct (Size_ 96, Kind 25)
prysm_data_include lvAdType
-- the two `fmt.Errorf` formats of the list rejects ("%d … %w")
prysm_data_include lvFmtTooBig
prysm_data_include lvFmtMis
-- error globals: addresses only (values are set by the runtime's package init)
prysm_data_include lvErrListTooBig
prysm_data_include lvErrIncorrectListSize
prysm_data_include lvErrInvalidVariableOffset

-- SyncAggregate and SyncCommittee
-- the element type word of the SyncCommittee `[][]byte` backing array (`make([][]byte, 512)`,
-- makeslice esz 24): abi.Type of `[]uint8`
prysm_data_include lvSliceType

-- DataColumnsByRootIdentifier decoder
-- "ssz-max exceeded: c.Columns has %d elements, ssz-max is 128: %w" (63 bytes)
prysm_data_include dcdFmtTooBig
-- "misaligned bytes: c.Columns length is %d, which is not a multiple of 8: %w" (74 bytes)
prysm_data_include dcdFmtMis

-- The address lemmas. `variable [Host]` comes after the data includes, so it binds only these lemmas.
variable [Host]

theorem e2eErrSize_addr_eq : ElfData.PrysmTarget.e2eErrSize_addr = (label "ssz.ErrSize").toBitVec := rfl
theorem e2eErrBytesLength_addr_eq : ElfData.PrysmTarget.e2eErrBytesLength_addr = (label "ssz.ErrBytesLength").toBitVec := rfl
theorem e2eStaticuint64s_addr_eq : ElfData.PrysmTarget.e2eStaticuint64s_addr = Runtime.Data.staticuint64s_addr := rfl
theorem lvErrIncorrectListSize_addr_eq : ElfData.PrysmTarget.lvErrIncorrectListSize_addr = (label "ssz.ErrIncorrectListSize").toBitVec := rfl
theorem lvErrListTooBig_addr_eq : ElfData.PrysmTarget.lvErrListTooBig_addr = (label "ssz.ErrListTooBig").toBitVec := rfl
theorem lvFmtMis_addr_eq : ElfData.PrysmTarget.lvFmtMis_addr = (label "go_string._" + 171319).toBitVec := rfl
theorem lvFmtTooBig_addr_eq : ElfData.PrysmTarget.lvFmtTooBig_addr = (label "go_string._" + 163839).toBitVec := rfl
theorem e2eIntType_addr_eq : ElfData.PrysmTarget.e2eIntType_addr = (label "type__" + 387520).toBitVec := rfl

end ElfData.PrysmTarget
