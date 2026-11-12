import E2eList.IaRejectCall
import Fk.RtErr
import Fk.BumpMore
import Fk.WHost

/-!
# Witnesses of `ia_e2e_reject_misaligned_nz` (P4) and `ia_e2e_reject_toobig_nz` (P5) (LV T3)

The premises of the corrected statements (`StmtIaNz.lean`) are satisfiable, `e0 ≠ 0` included, with a concrete
non-zero itab word. The text of `Fk/WitLuMa.lean` (the witness of the precedent `lu_reject_misaligned_main`).
Host: data labels (`go_string._` at 0x10001, the bump pointer label at 0x10004), the real Go 1.26.10
`(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (index 5), `RtErr` (284: `rt_convT64`, `rt_errorf_dw`), then the
labels `go_itab._errors.errorString_error` (0x1012b, the value of `e0`), `ssz.ErrIncorrectListSize` (0x1013b),
`ssz.ErrListTooBig` (0x1014b) and `runtime.staticuint64s` (0x1015b), with pad labels between (a label's address is
0x10000 plus its index). One memory block at 0x10000: the bump pointer, the type word of the itab (0 bytes), the two
error globals (itab, `e1` = 0x10170), the static entry of 1, the errorString object (message "err"), the frame
(rsp = 0x10300, `S = 8`), the guard word, the 4 offset bytes of the input (the decoder reads no more bytes on these
paths), the 8320-byte heap, and the two format strings at `go_string._ + 163839` and `go_string._ + 171319`. The
frame `R` is `fun _ => True` (every other byte of the block).
P4: len = 229 (len − 228 = 1, misaligned; the box of 1 is the static entry). P5: len = 228 + 8 · 2049 (2049 > 2048
elements; the box is on the heap).
-/

open Fk Fk.W E2eList E2eList.Code

namespace E2eList.WitIaR


def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "go_string._", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def tailLabels : Program := [.label "go_itab._errors.errorString_error", .label "pad_t0", .label "pad_t1", .label "pad_t2", .label "pad_t3", .label "pad_t4", .label "pad_t5", .label "pad_t6", .label "pad_t7", .label "pad_t8", .label "pad_t9", .label "pad_t10", .label "pad_t11", .label "pad_t12", .label "pad_t13", .label "pad_t14", .label "ssz.ErrIncorrectListSize", .label "pad_s0", .label "pad_s1", .label "pad_s2", .label "pad_s3", .label "pad_s4", .label "pad_s5", .label "pad_s6", .label "pad_s7", .label "pad_s8", .label "pad_s9", .label "pad_s10", .label "pad_s11", .label "pad_s12", .label "pad_s13", .label "pad_s14", .label "ssz.ErrListTooBig", .label "pad_u0", .label "pad_u1", .label "pad_u2", .label "pad_u3", .label "pad_u4", .label "pad_u5", .label "pad_u6", .label "pad_u7", .label "pad_u8", .label "pad_u9", .label "pad_u10", .label "pad_u11", .label "pad_u12", .label "pad_u13", .label "pad_u14", .label "runtime.staticuint64s"]

def P : Program := dataLabels ++ IaUnmarshal ++ RtErr ++ tailLabels

-- Measured cause (log 260): `rfl` on the 348-directive host program stops with "maximum recursion depth" at
-- the default (512) in `P_len` and `hk284` only; 1024 passes (log 261). The other host facts need no option.
set_option maxRecDepth 1024 in
theorem P_len : P.length = 348 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk5 : IaUnmarshal.IsInfixAt Host.prog 5 :=
  infixAt_of dataLabels (RtErr ++ tailLabels) (by simp [prog_eq, P, List.append_assoc]) rfl
set_option maxRecDepth 1024 in
theorem hk284 : RtErr.IsInfixAt Host.prog 284 :=
  infixAt_of (dataLabels ++ IaUnmarshal) tailLabels (by simp [prog_eq, P, List.append_assoc]) (by rfl)

theorem hf5 : LabelsFresh IaUnmarshal 5 := labelsFresh_of (by rw [prog_eq]; decide)
theorem hf284 : LabelsFresh RtErr 284 := labelsFresh_of (by rw [prog_eq]; decide)

theorem label_bump : label "runtime.fvBump" = 0x10004 :=
  mk_label P _ 4 _ (by simp [P, dataLabels]) (by decide)
theorem label_gs : label "go_string._" = 0x10001 :=
  mk_label P _ 1 _ (by simp [P, dataLabels]) (by decide)
theorem label_itab : label "go_itab._errors.errorString_error" = 0x1012b :=
  mk_label P _ 299 _ (by simp [P, dataLabels]; rfl) (by decide)
theorem label_mis : label "ssz.ErrIncorrectListSize" = 0x1013b :=
  mk_label P _ 315 _ (by simp [P, dataLabels]; rfl) (by decide)
theorem label_big : label "ssz.ErrListTooBig" = 0x1014b :=
  mk_label P _ 331 _ (by simp [P, dataLabels]; rfl) (by decide)
theorem label_st : label "runtime.staticuint64s" = 0x1015b :=
  mk_label P _ 347 _ (by simp [P, dataLabels]; rfl) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

def block : List UInt8 :=
  (z 4) ++ ((Int.toBytes 8 (0x10400 : BitVec 64).toInt) ++ ((z 295) ++ ((z 8) ++ ((Int.toBytes 8 (65835#64).toInt) ++ ((Int.toBytes 8 (65904#64).toInt) ++ ((Int.toBytes 8 (65835#64).toInt) ++ ((Int.toBytes 8 (65904#64).toInt) ++ ((z 8) ++ ((Int.toBytes 8 (1#64).toInt) ++ ((z 5) ++ ((Int.toBytes 8 (65920#64).toInt) ++ ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt) ++ (([101, 114, 114]) ++ ((z 189) ++ ((z 8) ++ ((z 8) ++ ((z 40) ++ ((z 56) ++ ((z 32) ++ ((z 32) ++ ((z 8) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ (([0xe4, 0, 0, 0]) ++ ((z 204) ++ ((z 8320) ++ ((z 154496) ++ ((E2eList.Data.lvFmtTooBig) ++ ((z 7407) ++ (E2eList.Data.lvFmtMis)))))))))))))))))))))))))))))))))))

def mem : DataMem := block.At (0x10000 : BitVec 64)

def s0 (len : Nat) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0, 0x10330, UInt64.ofNat len, 0, 0, UInt64.ofNat len, 0x10300, 0, 0, 0, 0, 0, 0, 0, 0x10310, 0⟩, zmms, flags, mem⟩

/-- **Non-vacuity of `ia_e2e_reject_misaligned_nz` (P4)**, len = 229, `e0` = the itab address 0x1012b (≠ 0). -/
theorem ia_misaligned_runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨s0 229 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (ia_e2e_reject_misaligned_nz 5 hk5 hf5 (s0 229 zmms flags) 0 0 65835 65904 (65920 : BitVec 64)
    [101, 114, 114] (z 8) (by rw [label_itab]; rfl) (by decide) rfl
    (z 8) (z 8) (z 32) (z 40) (z 8) (z 8) rfl rfl rfl rfl rfl 8 rfl bumpHeap 8320 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split [lvFmtMis_len, lvFmtTooBig_len]
      simp only [UInt64.toBitVec_ofNat] at H
      have H2 : ((Eq ((Int.toBytes 8 (66560#64).toInt).At 65540#64) ⋆ Eq ((z 8320).At 66560#64)) ⋆ (Eq ((z 4).At 65536#64) ⋆ Eq ((z 295).At 65548#64) ⋆ Eq ((z 8).At 65843#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65851#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65859#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65867#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65875#64) ⋆ Eq ((z 8).At 65883#64) ⋆ Eq ((Int.toBytes 8 (1#64).toInt).At 65891#64) ⋆ Eq ((z 5).At 65899#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65904#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65912#64) ⋆ Eq (([101, 114, 114]).At 65920#64) ⋆ Eq ((z 189).At 65923#64) ⋆ Eq ((z 8).At 66112#64) ⋆ Eq ((z 8).At 66120#64) ⋆ Eq ((z 40).At 66128#64) ⋆ Eq ((z 56).At 66168#64) ⋆ Eq ((z 32).At 66224#64) ⋆ Eq ((z 32).At 66256#64) ⋆ Eq ((z 8).At 66288#64) ⋆ Eq ((z 8).At 66296#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66304#64) ⋆ Eq ((z 8).At 66312#64) ⋆ Eq ((z 8).At 66320#64) ⋆ Eq ((z 8).At 66328#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66336#64) ⋆ Eq ((z 8).At 66344#64) ⋆ Eq (([228, 0, 0, 0]).At 66352#64) ⋆ Eq ((z 204).At 66356#64) ⋆ Eq ((z 154496).At 74880#64) ⋆ Eq ((E2eList.Data.lvFmtTooBig).At 229376#64) ⋆ Eq ((z 7407).At 229449#64) ⋆ Eq ((E2eList.Data.lvFmtMis).At 236856#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8320)
        (fun m hm => ⟨66560#64, by decide, by rw [label_bump]; exact hm⟩) H2
      apply sep_true
      simp only [s0, ErrStr, ErrObj, lvErrMis_addr_eq, lvFmtMis_addr_eq, label_mis, label_itab, label_gs,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceSub, Nat.reduceAdd, u64_toBitVec_ofNat, iaOff, List.length_cons, List.length_nil]
      rw [staticBox_of_lt (by decide), Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [Data.staticuint64s_addr, label_st, Int64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceMul, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 48 < (0x10300 : UInt64).toNat; decide)
    (by show 228 ≤ (UInt64.ofNat 229).toNat; decide)
    (by show ((UInt64.ofNat 229).toNat - 228) % 8 ≠ 0; decide) (by rw [lvFmtMis_len]; decide)
    (rt_convT64 284 hk284 hf284 8) (rt_errorf_dw 284 hk284 hf284 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)


/-- **Non-vacuity of `ia_e2e_reject_toobig_nz` (P5)**, len = 228 + 8 · 2049, `e0` = the itab address 0x1012b (≠ 0). -/
theorem ia_toobig_runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨s0 16620 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (ia_e2e_reject_toobig_nz 5 hk5 hf5 (s0 16620 zmms flags) 0 0 65835 65904 (65920 : BitVec 64)
    [101, 114, 114] (z 8) (by rw [label_itab]; rfl) (by decide) rfl
    (z 8) (z 8) (z 32) (z 40) (z 8) (z 8) rfl rfl rfl rfl rfl 8 rfl bumpHeap 8320 (fun _ => True)
    (by
      have H : Eq (block.At (0x10000 : BitVec 64)) mem := rfl
      wit_split [lvFmtMis_len, lvFmtTooBig_len]
      simp only [UInt64.toBitVec_ofNat] at H
      have H2 : ((Eq ((Int.toBytes 8 (66560#64).toInt).At 65540#64) ⋆ Eq ((z 8320).At 66560#64)) ⋆ (Eq ((z 4).At 65536#64) ⋆ Eq ((z 295).At 65548#64) ⋆ Eq ((z 8).At 65843#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65851#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65859#64) ⋆ Eq ((Int.toBytes 8 (65835#64).toInt).At 65867#64) ⋆ Eq ((Int.toBytes 8 (65904#64).toInt).At 65875#64) ⋆ Eq ((z 8).At 65883#64) ⋆ Eq ((Int.toBytes 8 (1#64).toInt).At 65891#64) ⋆ Eq ((z 5).At 65899#64) ⋆ Eq ((Int.toBytes 8 (65920#64).toInt).At 65904#64) ⋆ Eq ((Int.toBytes 8 (3#64).toInt).At 65912#64) ⋆ Eq (([101, 114, 114]).At 65920#64) ⋆ Eq ((z 189).At 65923#64) ⋆ Eq ((z 8).At 66112#64) ⋆ Eq ((z 8).At 66120#64) ⋆ Eq ((z 40).At 66128#64) ⋆ Eq ((z 56).At 66168#64) ⋆ Eq ((z 32).At 66224#64) ⋆ Eq ((z 32).At 66256#64) ⋆ Eq ((z 8).At 66288#64) ⋆ Eq ((z 8).At 66296#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66304#64) ⋆ Eq ((z 8).At 66312#64) ⋆ Eq ((z 8).At 66320#64) ⋆ Eq ((z 8).At 66328#64) ⋆ Eq ((Int.toBytes 8 (0#64).toInt).At 66336#64) ⋆ Eq ((z 8).At 66344#64) ⋆ Eq (([228, 0, 0, 0]).At 66352#64) ⋆ Eq ((z 204).At 66356#64) ⋆ Eq ((z 154496).At 74880#64) ⋆ Eq ((E2eList.Data.lvFmtTooBig).At 229376#64) ⋆ Eq ((z 7407).At 229449#64) ⋆ Eq ((E2eList.Data.lvFmtMis).At 236856#64))) mem := by ecancel
      have H3 := sep_mono_left (P' := bumpHeap 8320)
        (fun m hm => ⟨66560#64, by decide, by rw [label_bump]; exact hm⟩) H2
      apply sep_true
      simp only [s0, ErrStr, ErrObj, lvErrBig_addr_eq, lvFmtTooBig_addr_eq, label_big, label_itab, label_gs,
        UInt64.toBitVec_ofNat, Int64.toBitVec_ofNat, Int64.toBitVec_add, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd,
        BitVec.reduceSub, Nat.reduceAdd, iaOff, List.length_cons, List.length_nil]
      rw [UInt64.toNat_ofNat_of_lt' (by decide), show (16620 - 228) / 8 = 2049 from rfl]
      simp only [StaticBox, show ((BitVec.ofNat 64 2049).toNat < 256) = False from by decide, ↓reduceIte]
      rw [nil_At_emp, Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
      simp only [BitVec.reduceAdd, Int.toBytes_length]
      ecancel)
    (by show (0 : UInt64).toNat + 48 < (0x10300 : UInt64).toNat; decide)
    (by show 228 ≤ (UInt64.ofNat 16620).toNat; decide)
    (by show ((UInt64.ofNat 16620).toNat - 228) % 8 = 0; decide)
    (by show 2048 < ((UInt64.ofNat 16620).toNat - 228) / 8; decide) (by rw [lvFmtTooBig_len]; decide)
    (rt_convT64 284 hk284 hf284 8) (rt_errorf_dw 284 hk284 hf284 bumpHeap _ _ 8))
    (fun _ h => ⟨h.1, h.2.1⟩)

end E2eList.WitIaR
