import Fk.CpMarshal
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `cp_marshal_main` (1b-fix X4)

Host: data labels, the real Checkpoint.MarshalSSZTo (index 5) and `RtCopy`
(`rt_memmove`). For every epoch word, root and destination prefix `pre`
(any length up to 1000), `s0` meets every premise of `cp_marshal_main`
(fast path: capacity len + 40) and the function returns `dst[:len + 40]`.
-/

open Fk Fk.Code Fk.W

namespace Fk.WitCpM

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ PrysmCheckpointMarshalSSZTo ++ RtCopy

set_option maxRecDepth 100000 in
theorem P_len : P.length = 113 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk_target : PrysmCheckpointMarshalSSZTo.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨RtCopy, by simp [P, dataLabels]⟩

set_option maxRecDepth 100000 in
theorem hf_target : LabelsFresh PrysmCheckpointMarshalSSZTo 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hk_rtcopy : RtCopy.IsInfixAt Host.prog 87 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmCheckpointMarshalSSZTo).length = 87 := by
    simp only [List.length_append, show PrysmCheckpointMarshalSSZTo.length = 82 from by rfl]; rfl
  exact ⟨[], by rw [P, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem hf_rtcopy : LabelsFresh RtCopy 87 := labelsFresh_of (by rw [prog_eq]; decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

def block (e8 root pre : List UInt8) : List UInt8 :=
  (Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 72) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ (e8 ++ ((Int.toBytes 8 (0x100b0 : BitVec 64).toInt) ++ ((Int.toBytes 8 32) ++ (root ++ (pre ++ ((z 8) ++ ((z 32))))))))))))))))))

def mem (e8 root pre : List UInt8) : DataMem := (block e8 root pre).At (0x10000 : BitVec 64)

def s0 (e8 root pre : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10098, 0x100d0, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + 40), 0x10080, 0, 0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem e8 root pre⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem s_mem (e8 root pre : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32) (hpl : pre.length ≤ 1000) (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 e8 root pre zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (0x100b0 : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 16)) ⋆ Eq (root.At (0x100b0 : BitVec 64))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block e8 root pre).At (0x10000 : BitVec 64)) (mem e8 root pre) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length, he8, hroot]; try omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, he8, hroot,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  apply sep_true (F := Eq ((z 72).At 65552#64) ⋆ Eq ((z 8).At 65640#64) ⋆ Eq ((z 8).At 65672#64))
  have hu0 : (UInt64.toBitVec 0) = 0#64 := rfl
  have huN : ∀ n : Nat, (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := fun _ => rfl
  simp only [hu0, huN] at H ⊢
  refine Eq.mp ?_ H
  exact congrFun (by ac_rfl) _

/-- **Non-vacuity of `cp_marshal_main`.** Every premise holds in this host, the
memmove contract by `rt_memmove`; the encoder returns length `len(pre) + 40`. -/
theorem cp_marshal_runs (e8 root pre : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (hpl : pre.length ≤ 1000) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = pre.length + 40)
      ⟨s0 e8 root pre zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (cp_marshal_main 5 hk_target hf_target e8 root pre (z 8) (z 32) he8 hroot rfl rfl 0x100b0
    (s0 e8 root pre zmms flags) 0 0 (by simp [s0]; omega)
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] rfl (s_mem e8 root pre he8 hroot hpl zmms flags)
    (by simp [s0]) (by simp [s0]) (by simp [s0]; omega) (by simp [s0]; omega) (rt_memmove 87 hk_rtcopy hf_rtcopy 0))
    (fun _ h => ⟨h.1, by rw [h.2.2.1]; simp [s0]; omega⟩)

example (z : RegZmms) (f : StatusFlags) := cp_marshal_runs (List.replicate 8 1) (List.replicate 32 2) [] rfl rfl (by simp) z f
example (z : RegZmms) (f : StatusFlags) := cp_marshal_runs (List.replicate 8 1) (List.replicate 32 2) [7, 7, 7] rfl rfl (by simp) z f

end Fk.WitCpM
