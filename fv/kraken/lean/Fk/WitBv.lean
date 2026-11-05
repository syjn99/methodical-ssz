import Fk.BvAccept
import Fk.BumpMore
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `bv_accept_main` (1b-fix X4)

Host: data labels, the real BitVec.UnmarshalSSZ (index 5) and the 1-byte bump
`runtime.makeslice` (`bump_makeslice1`). For every input byte `b` (padding bits
included), `s0 b` meets every premise of `bv_accept_main` and the function
returns nil. The examples are b = 0 and b = 0x10 (finding F1: EthLib rejects
0x10, the machine accepts it).
-/

open Fk Fk.Code Fk.W

namespace Fk.WitBv

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ BitVecUnmarshalSSZ ++ BumpAlloc1

set_option maxRecDepth 100000 in
theorem P_len : P.length = 75 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk_target : BitVecUnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc1, by simp [P, dataLabels]⟩

set_option maxRecDepth 100000 in
theorem hk_makeslice : BumpAlloc1.IsInfixAt Host.prog 69 := by
  rw [prog_eq]
  have h : (dataLabels ++ BitVecUnmarshalSSZ).length = 69 := by
    simp only [List.length_append, show BitVecUnmarshalSSZ.length = 64 from by rfl]; rfl
  exact ⟨[], by rw [P, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem hf_target : LabelsFresh BitVecUnmarshalSSZ 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_makeslice : ∀ i < 69, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 69) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

set_option maxRecDepth 100000 in
theorem label_wb : label "runtime.writeBarrier" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

set_option maxRecDepth 100000 in
theorem label_bump : label "runtime.fvBump" = 0x10004 :=
  mk_label P _ 4 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

def block (b : UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ ((Int.toBytes 8 (0x1000c : BitVec 64).toInt) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 24) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ ([b] ++ ((z 8) ++ ((z 8) ++ ((z 8))))))))))))))

def mem (b : UInt8) : DataMem := (block b).At (0x10000 : BitVec 64)

def s0 (b : UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x1005d, 0x1005c, 1, 0, 0, 0, 0x10044, 0, 0, 0, 0, 0, 0, 0, 0x10004, 0⟩, zmms, flags, mem b⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem s_mem (b : UInt8)  (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 b zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 0))
      ⋆ Eq ((z 24).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ bumpHeap 8
      ⋆ Eq ([b].At s.regs.rbx.toBitVec)
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block b).At (0x10000 : BitVec 64)) (mem b) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : ((Eq ((Int.toBytes 8 (65548#64).toInt).At 65540#64) ⋆ Eq ((z 8).At 65548#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65556#64)
        ⋆ Eq ((z 8).At 65564#64)
        ⋆ Eq ((z 24).At 65572#64)
        ⋆ Eq ((z 8).At 65596#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65604#64)
        ⋆ Eq ((z 8).At 65612#64)
        ⋆ Eq ((z 8).At 65620#64)
        ⋆ Eq ([b].At 65628#64)
        ⋆ Eq ((z 8).At 65629#64)
        ⋆ Eq ((z 8).At 65637#64)
        ⋆ Eq ((z 8).At 65645#64))) (mem b) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 8) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  have H4 := sep_true (F := Std.ExtHashMap.emp) (by simpa only [Std.ExtHashMap.sep_emp] using H3)
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H4 ⊢
  ac_nf at H4 ⊢

/-- **Non-vacuity of `bv_accept_main`.** Every premise holds in this host, the
makeslice contract by `bump_makeslice1`; the function returns nil. -/
theorem bv_accept_runs (b : UInt8) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨s0 b zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (bv_accept_main 5 hk_target hf_target b (s0 b zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] (z 24) rfl rfl bumpHeap 8 (s_mem b zmms flags)
    (by simp [s0]) (by simp [s0]) rfl (by omega) (bump_makeslice1 69 hk_makeslice hf_makeslice _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

example (z : RegZmms) (f : StatusFlags) := bv_accept_runs 0 z f
example (z : RegZmms) (f : StatusFlags) := bv_accept_runs 0x10 z f

end Fk.WitBv
