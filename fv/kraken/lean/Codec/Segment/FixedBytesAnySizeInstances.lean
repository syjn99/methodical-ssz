import Codec.Segment.FixedBytesAnySize
import Prysm.Deposit_Data.DecodeFieldSegmentPadding

/-!
# The hand fixed-size segment lemmas as one-line instances of `Codec.Segment.FixedBytesAnySize`

Each theorem below has as its type the type of a hand lemma (`type_of%`), and its proof applies the general
lemma. So every hand statement follows from the general one (new names; `Codec/FixedBytesDecode.lean`, `Prysm/SyncAggregate/DecodeFieldSegments.lean` and
`Prysm/Deposit_Data/DecodeFieldSegmentPadding.lean` are unchanged). The templates with a literal size are the general templates (`rfl`).
-/

open Machine Runtime Codec

namespace Codec.Segment

theorem bytesDecHeadNop96_eq : Prysm.SyncAggregate.bytesDecHeadNop96 = bytesDecHeadNopAnySize 96 := rfl
theorem bytesDecHeadNop32_eq : Prysm.Deposit_Data.bytesDecHeadNop = bytesDecHeadNopAnySize 32 := rfl

/-- `Codec.bytesdec_seg` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_inst : type_of% @Codec.bytesdec_seg :=
  fun n hn => bytesdec_seg_any_size n (by rcases hn with h | h | h <;> omega)
/-- `Codec.bytesdec_seg_offset_zero` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_offset_zero_inst : type_of% @Codec.bytesdec_seg_offset_zero :=
  fun n hn => bytesdec_seg_offset_zero_any_size n (by rcases hn with h | h | h <;> omega)
/-- `Prysm.SyncAggregate.bytesdec_seg_offset_zero_size64` (n = 64, SyncAggregate.SyncCommitteeBits). -/
theorem bytesdec_seg_offset_zero_size64_inst : type_of% @Prysm.SyncAggregate.bytesdec_seg_offset_zero_size64 :=
  fun n hn => bytesdec_seg_offset_zero_any_size n (by omega)
/-- `Prysm.SyncAggregate.bytes96dec_seg_nop` (SyncAggregate.SyncCommitteeSignature). -/
theorem bytes96dec_seg_nop_inst : type_of% @Prysm.SyncAggregate.bytes96dec_seg_nop :=
  by exact bytesdec_seg_nop_any_size 96 (by decide)
/-- `Prysm.Deposit_Data.bytes32dec_seg_nop` (Deposit_Data WithdrawalCredentials). -/
theorem bytes32dec_seg_nop_inst : type_of% @Prysm.Deposit_Data.bytes32dec_seg_nop :=
  by exact bytesdec_seg_nop_any_size 32 (by decide)

end Codec.Segment
