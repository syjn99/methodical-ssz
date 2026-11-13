import Codec.Segment.FixedBytesAnySize
import Prysm.Deposit_Data.DecodeFieldSegmentPadding

/-!
# The hand fixed-size segment lemmas as one-line instances of `Codec.Segment.FixedBytesAnySize`

Each theorem below has as its type the type of a hand lemma (`type_of%`), and its proof applies the general
lemma. So every hand statement follows from the general one (new names; `SegN.lean`, `Seg.lean` and
`DdSegNop.lean` are unchanged). The templates with a literal size are the general templates (`rfl`).
-/

open Machine Runtime TestTarget Codec

namespace Codec.Segment

theorem headNop96_eq : Prysm.SyncAggregate.bytesDecHeadNop96 = bytesDecHeadNopG 96 := rfl
theorem headNop32_eq : Prysm.Deposit_Data.bytesDecHeadNop = bytesDecHeadNopG 32 := rfl

/-- `Codec.bytesdec_seg` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_inst : type_of% @Codec.bytesdec_seg :=
  fun n hn => bytesdec_seg_g n (by rcases hn with h | h | h <;> omega)
/-- `Codec.bytesdec_seg_z` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_z_inst : type_of% @Codec.bytesdec_seg_z :=
  fun n hn => bytesdec_seg_z_g n (by rcases hn with h | h | h <;> omega)
/-- `Prysm.SyncAggregate.bytesdec_seg_z64` (n = 64, SyncAggregate.SyncCommitteeBits). -/
theorem bytesdec_seg_z64_inst : type_of% @Prysm.SyncAggregate.bytesdec_seg_z64 :=
  fun n hn => bytesdec_seg_z_g n (by omega)
/-- `Prysm.SyncAggregate.bytes96dec_seg_nop` (SyncAggregate.SyncCommitteeSignature). -/
theorem bytes96dec_seg_nop_inst : type_of% @Prysm.SyncAggregate.bytes96dec_seg_nop :=
  by exact bytesdec_seg_nop_g 96 (by decide)
/-- `Prysm.Deposit_Data.bytes32dec_seg_nop` (Deposit_Data WithdrawalCredentials). -/
theorem bytes32dec_seg_nop_inst : type_of% @Prysm.Deposit_Data.bytes32dec_seg_nop :=
  by exact bytesdec_seg_nop_g 32 (by decide)

end Codec.Segment
