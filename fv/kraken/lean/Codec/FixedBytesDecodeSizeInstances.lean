import Codec.Kind.FixedBytesDecode
import Codec.Kind.FieldPatterns
import Codec.Kind.Bytes32DecodeOffsetZero
import Prysm.DepositMessage.DecodeFieldSegmentOffsetZero

/-!
# The existing 32-byte / 48-byte lemmas and kinds are instances of the size-parametric ones

Every theorem here is a definitional identity (`rfl`); none is a stated equivalence. The existing files
(`P2Dec.lean`, `P2DecZ.lean`, `DmSeg0.lean`, `Kind.lean`, `KindZ.lean`) are unchanged and their lemmas are not
re-proved from the new ones: the new lemmas run the same proof text again.

* templates: `rootDecHead = bytesDecHead 32`, `rootDecMid = bytesDecMid 32`, `rootDecMidZ = bytesDecMidZ 32`,
  `Prysm.DepositMessage.bytesDecHead48 = bytesDecHead 48`, `Prysm.DepositMessage.bytesDecMidZ48 = bytesDecMidZ 48`;
* kinds: `rootDecSegKind = bytesDecSegKind 32`, `rootDecSegZKind = bytesDecSegZKind 32` (`with_reducible rfl`:
  only instances and the two `abbrev`s unfold);
* lemma statements: the declared type of `rootdec_seg`, `rootdec_seg_z` and `Prysm.DepositMessage.bytes48dec_seg_z` is the
  declared type of `bytesdec_seg 32 _`, `bytesdec_seg_z 32 _` and `bytesdec_seg_z 48 _` (`rfl` at default
  transparency: the template definitions unfold).
-/

open Machine Runtime TestTarget

open Codec
namespace Codec

theorem rootDecHead_eq_bytes : rootDecHead = bytesDecHead 32 := rfl
theorem rootDecMid_eq_bytes : rootDecMid = bytesDecMid 32 := rfl
theorem rootDecMidZ_eq_bytes : rootDecMidZ = bytesDecMidZ 32 := rfl
theorem bytesDecHead48_eq_bytes : Prysm.DepositMessage.bytesDecHead48 = bytesDecHead 48 := rfl
theorem bytesDecMidZ48_eq_bytes : Prysm.DepositMessage.bytesDecMidZ48 = bytesDecMidZ 48 := rfl

theorem rootDecSegKind_eq_bytes : ∀ (h : Host) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC src : Int64),
    @rootDecSegKind h C j1 j2 dR dB dS fP fL fC src = @bytesDecSegKind h 32 C j1 j2 dR dB dS fP fL fC src := by
  intros; with_reducible rfl

theorem rootDecSegZKind_eq_bytes : ∀ (h : Host) (C : Program) (j1 j2 : Nat) (dR dB dS fP fL fC : Int64),
    @rootDecSegZKind h C j1 j2 dR dB dS fP fL fC = @bytesDecSegZKind h 32 C j1 j2 dR dB dS fP fL fC := by
  intros; with_reducible rfl

theorem rootdec_seg_is_bytes32 : ∀ (h : Host),
    type_of% (@rootdec_seg h) = type_of% (@bytesdec_seg h 32 (Or.inl rfl)) := by
  intro h; rfl

theorem rootdec_seg_z_is_bytes32 : ∀ (h : Host),
    type_of% (@rootdec_seg_z h) = type_of% (@bytesdec_seg_z h 32 (Or.inl rfl)) := by
  intro h; rfl

theorem bytes48dec_seg_z_is_bytes48 : ∀ (h : Host),
    type_of% (@Prysm.DepositMessage.bytes48dec_seg_z h) = type_of% (@bytesdec_seg_z h 48 (Or.inr (Or.inl rfl))) := by
  intro h; rfl

end Codec
