import Kraken.X64.WP
import Fk.Include

/-!
# ELF data that the proofs read (fix 3 X2)

Every definition here is elaborated from a file of `link/out/data/` by
`data_include` (`Fk/Include.lean`); `link/data.py` writes the files from the
ELF, `link/check.py` compares them with the ELF, and the files are Lake inputs
of the `Fk` library. No byte and no offset below is written by hand.
Interface (names, file format, item table): `TOOLS.md`, "ELF 데이터 include".

The theorems keep their premises in the form `Eq (bytes.At addr)`; `bytes` and
`addr` come from here. Kraken's data memory is separate from the code: these
are facts about the data at the labels' addresses, as premises.

The lemmas at the end state, about the included bytes, what the old link check (h)
checked by regular expressions: the type descriptors' size and kind, the
itab's type word and method, the `staticuint64s` table.
-/

namespace Fk.Data

-- rodata strings (`go:string.*`): format strings and messages
data_include blFmtB
data_include bvFmtJ
data_include vbvFmt
data_include lcFmtZero
data_include lcFmtShort
data_include lcFmtOrder
data_include vblMsgE
data_include vblMsgZ
data_include vblMsgB
data_include luFmtTooBig
data_include luFmtMis
data_include lcFmtItems
-- runtime data: the errorString itab, type descriptors, the static box table
data_include errorStringItab
data_include errorStringPtrType
data_include intType
data_include uint64Type
data_include staticuint64s
-- error globals: addresses only (their values are set by the runtime's init)
data_include ErrSize
data_include ErrInvalidSerialization
data_include ErrInvalidVariableOffset
data_include ErrListTooBig
data_include ErrBytesLength
data_include ErrIncorrectListSize

section
variable [Host]

/-- `abi.Type` header fields of a descriptor: `Size_` (bytes 0–7) and `Kind_`
(byte 23, low 5 bits; Go 1.26.3 internal/abi/type.go). -/
def typeSize (t : List UInt8) : List UInt8 := t.take 8
def typeKind (t : List UInt8) : Nat := (t.getD 23 0).toNat % 32

/-- `int`: size 8, kind `Int` (2). -/
theorem intType_size_kind : typeSize intType = [8, 0, 0, 0, 0, 0, 0, 0] ∧ typeKind intType = 2 :=
  ⟨rfl, rfl⟩

/-- `uint64`: size 8, kind `Uint64` (11). -/
theorem uint64Type_size_kind : typeSize uint64Type = [8, 0, 0, 0, 0, 0, 0, 0] ∧ typeKind uint64Type = 11 :=
  ⟨rfl, rfl⟩

/-- `*errors.errorString`: size 8, kind `Pointer` (22), and its `Elem` (bytes
48–55) is the descriptor at `type__ + 82848`, the type that the generated code
passes to `runtime.newobject` for a new `errors.errorString`. -/
theorem errorStringPtrType_shape :
    typeSize errorStringPtrType = [8, 0, 0, 0, 0, 0, 0, 0] ∧ typeKind errorStringPtrType = 22 ∧
    errorStringPtrType.drop 48 = Int.toBytes 8 (label "type__" + 82848).toBitVec.toInt :=
  ⟨rfl, rfl, rfl⟩

theorem errorStringPtrType_len : errorStringPtrType.length = 56 := by
  simp [errorStringPtrType, Int.toBytes_length]

/-- The errorString itab: its type word (bytes 8–15, read by the `%w` paths at
`itab + 8`) is the address of `errorStringPtrType`, and its one method
(`Fun[0]`, bytes 24–31) is `errors.(*errorString).Error`. -/
theorem errorStringItab_shape :
    (errorStringItab.drop 8).take 8 = Int.toBytes 8 errorStringPtrType_addr.toInt ∧
    errorStringItab.drop 24 = Int.toBytes 8 (label "errors.errorString.Error").toBitVec.toInt :=
  ⟨rfl, rfl⟩

end

/-- `runtime.staticuint64s` is the table of the uint64 values 0..255. Checked by
the kernel (`decide +kernel`: no `Lean.ofReduceBool`, unlike `native_decide`). -/
theorem staticuint64s_table : staticuint64s = (List.range 256).flatMap (fun i : Nat => Int.toBytes 8 (i : Int)) := by
  decide +kernel

end Fk.Data

namespace Fk
/-! The rodata items under their names in `Fk` (aliases of `Fk.Data.*`; no new
constants): the theorems and witnesses name them as before. -/
export Data (blFmtB blFmtB_addr bvFmtJ bvFmtJ_addr vbvFmt vbvFmt_addr lcFmtZero lcFmtZero_addr
  lcFmtShort lcFmtShort_addr lcFmtOrder lcFmtOrder_addr vblMsgE vblMsgE_addr vblMsgZ vblMsgZ_addr
  vblMsgB vblMsgB_addr luFmtTooBig luFmtTooBig_addr luFmtMis luFmtMis_addr intType_addr uint64Type_addr
  errorStringPtrType errorStringPtrType_len lcFmtItems lcFmtItems_addr)
end Fk
