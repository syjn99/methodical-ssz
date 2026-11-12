import E2eSeg.SegG
import E2eScal.DdSegNop

/-!
# The hand fixed-size segment lemmas as one-line instances of `E2eSeg.SegG`

Each theorem below has as its type the type of a hand lemma (`type_of%`), and its proof applies the general
lemma. So every hand statement follows from the general one (new names; `SegN.lean`, `Seg.lean` and
`DdSegNop.lean` are unchanged). The templates with a literal size are the general templates (`rfl`).
-/

open Fk E2eScal

namespace E2eSeg

theorem headNop96_eq : E2eList.bytesDecHeadNop96 = bytesDecHeadNopG 96 := rfl
theorem headNop32_eq : E2eScal.H4.bytesDecHeadNop = bytesDecHeadNopG 32 := rfl

/-- `E2eScal.bytesdec_seg` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_inst : type_of% @E2eScal.bytesdec_seg :=
  fun n hn => bytesdec_seg_g n (by rcases hn with h | h | h <;> omega)
/-- `E2eScal.bytesdec_seg_z` (n ∈ {32, 48, 96}). -/
theorem bytesdec_seg_z_inst : type_of% @E2eScal.bytesdec_seg_z :=
  fun n hn => bytesdec_seg_z_g n (by rcases hn with h | h | h <;> omega)
/-- `E2eList.bytesdec_seg_z64` (n = 64, T1 SyncCommitteeBits). -/
theorem bytesdec_seg_z64_inst : type_of% @E2eList.bytesdec_seg_z64 :=
  fun n hn => bytesdec_seg_z_g n (by omega)
/-- `E2eList.bytes96dec_seg_nop` (T1 SyncCommitteeSignature). -/
theorem bytes96dec_seg_nop_inst : type_of% @E2eList.bytes96dec_seg_nop :=
  by exact bytesdec_seg_nop_g 96 (by decide)
/-- `E2eScal.H4.bytes32dec_seg_nop` (Deposit_Data WithdrawalCredentials). -/
theorem bytes32dec_seg_nop_inst : type_of% @E2eScal.H4.bytes32dec_seg_nop :=
  by exact bytesdec_seg_nop_g 32 (by decide)

end E2eSeg
