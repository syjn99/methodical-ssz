import Codec.Kind.FixedBytesDecode
import Codec.Kind.FieldPatterns
import Codec.Kind.Bytes32DecodeOffsetZero
import Prysm.DepositMessage.DecodeFieldSegmentOffsetZero

/-!
# The existing 32-byte / 48-byte lemmas and kinds are instances of the size-parametric ones

Every theorem here is a definitional identity (`rfl`); none is a stated equivalence. The existing files
(`Codec/Bytes32Decode.lean`, `Codec/Bytes32DecodeOffsetZero.lean`, `Prysm/DepositMessage/DecodeFieldSegmentOffsetZero.lean`, `Codec/Kind/FieldPatterns.lean`, `Codec/Kind/Bytes32DecodeOffsetZero.lean`) are unchanged and their lemmas are not
re-proved from the new ones: the new lemmas run the same proof text again.

* templates: `rootDecodeHead = bytesDecodeHead 32`, `rootDecodeMiddle = bytesDecodeMiddle 32`, `rootDecodeMiddleOffsetZero = bytesDecodeMiddleOffsetZero 32`,
  `Prysm.DepositMessage.bytesDecodeHead48 = bytesDecodeHead 48`, `Prysm.DepositMessage.bytesDecodeMiddleOffsetZero48 = bytesDecodeMiddleOffsetZero 48`;
* kinds: `rootDecodeSegmentKind = bytesDecodeSegmentKind 32`, `rootDecodeSegmentOffsetZeroKind = bytesDecodeSegmentOffsetZeroKind 32` (`with_reducible rfl`:
  only instances and the two `abbrev`s unfold);
* lemma statements: the declared type of `root_decode_segment`, `root_decode_segment_offset_zero` and `Prysm.DepositMessage.bytes48_decode_segment_offset_zero` is the
  declared type of `bytes_decode_segment 32 _`, `bytes_decode_segment_offset_zero 32 _` and `bytes_decode_segment_offset_zero 48 _` (`rfl` at default
  transparency: the template definitions unfold).
-/

open Machine Runtime

open Codec
namespace Codec

theorem rootDecodeHead_eq_bytes : rootDecodeHead = bytesDecodeHead 32 := rfl
theorem rootDecodeMiddle_eq_bytes : rootDecodeMiddle = bytesDecodeMiddle 32 := rfl
theorem rootDecodeMiddleOffsetZero_eq_bytes : rootDecodeMiddleOffsetZero = bytesDecodeMiddleOffsetZero 32 := rfl
theorem bytesDecodeHead48_eq_bytes : Prysm.DepositMessage.bytesDecodeHead48 = bytesDecodeHead 48 := rfl
theorem bytesDecodeMiddleOffsetZero48_eq_bytes : Prysm.DepositMessage.bytesDecodeMiddleOffsetZero48 = bytesDecodeMiddleOffsetZero 48 := rfl

theorem rootDecodeSegmentKind_eq_bytes : ∀ (h : Host) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC src : Int64),
    @rootDecodeSegmentKind h C j1 j2 dR dB dS fP fL fC src = @bytesDecodeSegmentKind h 32 C j1 j2 dR dB dS fP fL fC src := by
  intros; with_reducible rfl

theorem rootDecodeSegmentOffsetZeroKind_eq_bytes : ∀ (h : Host) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC : Int64),
    @rootDecodeSegmentOffsetZeroKind h C j1 j2 dR dB dS fP fL fC = @bytesDecodeSegmentOffsetZeroKind h 32 C j1 j2 dR dB dS fP fL fC := by
  intros; with_reducible rfl

theorem root_decode_segment_is_bytes32 : ∀ (h : Host),
    type_of% (@root_decode_segment h) = type_of% (@bytes_decode_segment h 32 (Or.inl rfl)) := by
  intro h; rfl

theorem root_decode_segment_offset_zero_is_bytes32 : ∀ (h : Host),
    type_of% (@root_decode_segment_offset_zero h) = type_of% (@bytes_decode_segment_offset_zero h 32 (Or.inl rfl)) := by
  intro h; rfl

theorem bytes48_decode_segment_offset_zero_is_bytes48 : ∀ (h : Host),
    type_of% (@Prysm.DepositMessage.bytes48_decode_segment_offset_zero h) = type_of% (@bytes_decode_segment_offset_zero h 48 (Or.inr (Or.inl rfl))) := by
  intro h; rfl

end Codec
