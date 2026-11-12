import E2eScal.KindAccept
import E2eScal.Gen2BiAccept
import E2eScal.Gen2DmAccept
import E2eScal.Gen2E1Accept

/-!
# The three generated composed accept theorems have the kind `decAcceptKind`

The declared type of each in-sample generated composed theorem (`Gen2BiAccept.lean`, `Gen2DmAccept.lean`,
`Gen2E1Accept.lean`; generator output, unchanged) is `decAcceptKind` at the parameters of its type, by `rfl`
at default transparency. This is the `_kind` line a generated composed theorem of this shape can carry
instead of the identity with a hand theorem.
-/

open Fk

namespace E2eScal

theorem bi_accept_gc_kind : ∀ (h : Host), type_of% (@E2eScal.Gen.bi_e2e_accept_main_gc h)
    = @decAcceptKind h E2eScal.H3Code.BiUnmarshal true [.bytes 32, .u64] 32 := by
  intro h; rfl

theorem dm_accept_gc_kind : ∀ (h : Host), type_of% (@E2eScal.Gen.dm_e2e_accept_main_gc h)
    = @decAcceptKind h E2eScal.H3Code.DmUnmarshal false [.bytes 48, .bytes 32, .u64] 68 := by
  intro h; rfl

theorem e1_accept_gc_kind : ∀ (h : Host), type_of% (@E2eScal.Gen.e1_e2e_accept_main_gc h)
    = @decAcceptKind h E2eScal.E1Code.E1Unmarshal true [.bytes 32, .u64, .bytes 32] 70 := by
  intro h; rfl

end E2eScal
