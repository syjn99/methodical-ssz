import E2eScal.Kind
import E2eAd.Prims

/-!
# Anchors of the P1 statement kind (review fix-r1 S1)

The P1 kind `E2eScal.u64DecAcceptKind C` is, for `C = SlUnmarshal` and `C = CiUnmarshal`, the full declared
type of the reviewed hand theorem (binders before the colon included). So the frozen kind is the hand
statement kind, not new text. P2 decode has no hand theorem of the segment shape; its kind is tied to the
lemma by `E2eScal.rootDecSegKind_of` only.
-/

open Fk E2eAd.Code

namespace E2eScal

theorem sl_kind_anchor : ∀ (h : Host), type_of% (@E2eAd.sl_unmarshal_accept_main h)
    = @u64DecAcceptKind h SlUnmarshal := by
  intro h; with_reducible rfl

theorem ci_kind_anchor : ∀ (h : Host), type_of% (@E2eAd.ci_unmarshal_accept_main h)
    = @u64DecAcceptKind h CiUnmarshal := by
  intro h; with_reducible rfl

end E2eScal
