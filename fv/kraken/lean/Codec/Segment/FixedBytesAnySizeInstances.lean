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

theorem bytesDecodeHeadNop96_eq : Prysm.SyncAggregate.bytesDecodeHeadNop96 = bytesDecodeHeadNopAnySize 96 := rfl
theorem bytesDecodeHeadNop32_eq : Prysm.Deposit_Data.bytesDecodeHeadNop = bytesDecodeHeadNopAnySize 32 := rfl

/-- `Codec.bytes_decode_segment` (n ∈ {32, 48, 96}). -/
theorem bytes_decode_segment_inst : type_of% @Codec.bytes_decode_segment :=
  fun n hn => bytes_decode_segment_any_size n (by rcases hn with h | h | h <;> omega)
/-- `Codec.bytes_decode_segment_offset_zero` (n ∈ {32, 48, 96}). -/
theorem bytes_decode_segment_offset_zero_inst : type_of% @Codec.bytes_decode_segment_offset_zero :=
  fun n hn => bytes_decode_segment_offset_zero_any_size n (by rcases hn with h | h | h <;> omega)
/-- `Prysm.SyncAggregate.bytes_decode_segment_offset_zero_size64` (n = 64, SyncAggregate.SyncCommitteeBits). -/
theorem bytes_decode_segment_offset_zero_size64_inst : type_of% @Prysm.SyncAggregate.bytes_decode_segment_offset_zero_size64 :=
  fun n hn => bytes_decode_segment_offset_zero_any_size n (by omega)
/-- `Prysm.SyncAggregate.bytes96_decode_segment_nop` (SyncAggregate.SyncCommitteeSignature). -/
theorem bytes96_decode_segment_nop_inst : type_of% @Prysm.SyncAggregate.bytes96_decode_segment_nop :=
  by exact bytes_decode_segment_nop_any_size 96 (by decide)
/-- `Prysm.Deposit_Data.bytes32_decode_segment_nop` (Deposit_Data WithdrawalCredentials). -/
theorem bytes32_decode_segment_nop_inst : type_of% @Prysm.Deposit_Data.bytes32_decode_segment_nop :=
  by exact bytes_decode_segment_nop_any_size 32 (by decide)

end Codec.Segment
