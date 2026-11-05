import Fk.AdMarshal
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `ad_marshal_main` (1b-fix X4)

Host: data labels, the real AttestationData.MarshalSSZTo (index 5) and
`RtCopy` (`rt_memmove`). For every 128 bytes of field values and every
3-byte destination prefix, `s0` meets every premise of `ad_marshal_main`
(three memmove calls) and the encoder returns length 3 + 128.
A symbolic prefix length made the memory lemma time out (REPORT-1b-fix X4).
-/

open Fk Fk.Code Fk.W

namespace Fk.WitAdM

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ PrysmAttestationDataMarshalSSZTo ++ RtCopy

set_option maxRecDepth 100000 in
theorem P_len : P.length = 366 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk_target : PrysmAttestationDataMarshalSSZTo.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨RtCopy, by simp [P, dataLabels]⟩

set_option maxRecDepth 100000 in
theorem hf_target : LabelsFresh PrysmAttestationDataMarshalSSZTo 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hk_rtcopy : RtCopy.IsInfixAt Host.prog 340 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmAttestationDataMarshalSSZTo).length = 340 := by
    simp only [List.length_append, show PrysmAttestationDataMarshalSSZTo.length = 335 from by rfl]; rfl
  exact ⟨[], by rw [show P = (dataLabels ++ PrysmAttestationDataMarshalSSZTo) ++ (RtCopy ++ []) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩

set_option maxRecDepth 100000 in
theorem hf_rtcopy : LabelsFresh RtCopy 340 := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

def block (e0 e1 root se sroot te troot pre : List UInt8) : List UInt8 :=
  (Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 88) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 32) ++ ((z 8) ++ ((z 8) ++ ((z 56) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ (e0 ++ (e1 ++ ((Int.toBytes 8 (0x10148 : BitVec 64).toInt) ++ ((Int.toBytes 8 32) ++ ((z 8) ++ ((Int.toBytes 8 (0x10168 : BitVec 64).toInt) ++ ((Int.toBytes 8 (0x101a0 : BitVec 64).toInt) ++ (root ++ (se ++ ((Int.toBytes 8 (0x10180 : BitVec 64).toInt) ++ ((Int.toBytes 8 32) ++ (sroot ++ (te ++ ((Int.toBytes 8 (0x101b8 : BitVec 64).toInt) ++ ((Int.toBytes 8 32) ++ (troot ++ (pre ++ ((z 8) ++ ((z 8) ++ ((z 32) ++ ((z 8) ++ ((z 32) ++ ((z 8) ++ ((z 32)))))))))))))))))))))))))))))))))))))))

def mem (e0 e1 root se sroot te troot pre : List UInt8) : DataMem := (block e0 e1 root se sroot te troot pre).At (0x10000 : BitVec 64)

def s0 (e0 e1 root se sroot te troot pre : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10110, 0x101d8, 3, 0, 0, 131, 0x100f8, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem e0 e1 root se sroot te troot pre⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem s_mem (e0 e1 root se sroot te troot pre : List UInt8) (h0 : e0.length = 8) (h1 : e1.length = 8) (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32) (hpl : pre.length = 3) (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 e0 e1 root se sroot te troot pre zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 72)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 136)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 240)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 240 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e0.At s.regs.rax.toBitVec) ⋆ Eq (e1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 (0x10148 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 (0x10168 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 (0x101a0 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (root.At (0x10148 : BitVec 64))
      ⋆ Eq (se.At (0x10168 : BitVec 64)) ⋆ Eq ((Int.toBytes 8 (0x10180 : BitVec 64).toInt).At ((0x10168 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 32).At ((0x10168 : BitVec 64) + 16))
      ⋆ Eq (sroot.At (0x10180 : BitVec 64))
      ⋆ Eq (te.At (0x101a0 : BitVec 64)) ⋆ Eq ((Int.toBytes 8 (0x101b8 : BitVec 64).toInt).At ((0x101a0 : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 32).At ((0x101a0 : BitVec 64) + 16))
      ⋆ Eq (troot.At (0x101b8 : BitVec 64))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96)) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block e0 e1 root se sroot te troot pre).At (0x10000 : BitVec 64)) (mem e0 e1 root se sroot te troot pre) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, h0, h1, hroot, hse, hsroot, hte, htroot, hpl]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, h0, h1, hroot, hse, hsroot, hte, htroot, hpl,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  apply sep_true (F := Eq ((z 88).At 65552#64) ⋆ Eq ((z 32).At 65672#64) ⋆ Eq ((z 56).At 65720#64) ⋆ Eq ((z 8).At 65840#64))
  have hu0 : (UInt64.toBitVec 0) = 0#64 := rfl
  have huN : ∀ n : Nat, (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := fun _ => rfl
  simp only [hu0, huN] at H ⊢
  refine Eq.mp ?_ H
  exact congrFun (by ac_rfl) _

/-- **Non-vacuity of `ad_marshal_main`.** Every premise holds in this host, the
memmove contract by `rt_memmove`; the encoder returns length 3 + 128. -/
theorem ad_marshal_runs (e0 e1 root se sroot te troot pre : List UInt8) (h0 : e0.length = 8) (h1 : e1.length = 8) (hroot : root.length = 32)
    (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (hpl : pre.length = 3) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = 3 + 128)
      ⟨s0 e0 e1 root se sroot te troot pre zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (ad_marshal_main 5 hk_target hf_target e0 e1 root se sroot te troot pre (z 8) (z 8) (z 32) (z 8) (z 32) (z 8) (z 32)
    h0 h1 hroot hse hsroot hte htroot rfl rfl rfl rfl rfl rfl rfl
    0x10148 0x10168 0x101a0 0x10180 0x101b8
    (s0 e0 e1 root se sroot te troot pre zmms flags) 0 0 (by simp [s0, hpl])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] rfl (s_mem e0 e1 root se sroot te troot pre h0 h1 hroot hse hsroot hte htroot hpl zmms flags)
    (by decide) (by decide) (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])
    (rt_memmove 340 hk_rtcopy hf_rtcopy 0))
    (fun _ h => ⟨h.1, by rw [h.2.2.1]; simp [s0]⟩)

end Fk.WitAdM
