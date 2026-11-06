import Fk.FvAccept
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `fv_accept_main` (1b-fix X4)

Host: data labels (write barrier, three pads, bump pointer), then the real
FixedVec.UnmarshalSSZ (index 5), the bump `runtime.makeslice` (index 91,
`bump_makeslice`, 8-byte elements) and `RtCopy` (index 97, `rt_memmove`).
For every input (`rb`: 32 bytes, `ws`: 32 bytes) the state `fs0` meets every
premise of `fv_accept_main`, both contracts included, and the function returns
nil. FixedVec has a fixed size, so one shape covers all inputs.
-/

open Fk Fk.Code Fk.W

namespace Fk.WitFv

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ FixedVecUnmarshalSSZ ++ BumpAlloc ++ RtCopy

set_option maxRecDepth 100000 in
theorem P_len : P.length = 123 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk5 : FixedVecUnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc ++ RtCopy, by simp [P, dataLabels]⟩

theorem hk91 : BumpAlloc.IsInfixAt Host.prog 91 := by
  rw [prog_eq]
  have h : (dataLabels ++ FixedVecUnmarshalSSZ).length = 91 := by
    rw [List.length_append, show FixedVecUnmarshalSSZ.length = 86 from by rfl]; rfl
  exact ⟨RtCopy, by rw [P, List.append_assoc, ← h, List.drop_left]⟩

theorem hk97 : RtCopy.IsInfixAt Host.prog 97 := by
  rw [prog_eq]
  have h : (dataLabels ++ FixedVecUnmarshalSSZ ++ BumpAlloc).length = 97 := by
    rw [List.length_append, List.length_append, show FixedVecUnmarshalSSZ.length = 86 from by rfl]; rfl
  exact ⟨[], by rw [P, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem hf5 : LabelsFresh FixedVecUnmarshalSSZ 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf97 : LabelsFresh RtCopy 97 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf91 : ∀ i < 91, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 91) := by decide
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

/-- Data memory from 0x10000: write barrier (4), bump pointer (8), heap (32),
stack guard (8), stack (rslot, spill 24, saved rbp, return address, two spill
slots), input (64), receiver (56). -/
def block (rb ws : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ (Int.toBytes 8 (0x10010 : BitVec 64).toInt ++ ((z 4) ++ (z 32) ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt
    ++ (z 8 ++ (z 24 ++ (z 8 ++ (Int.toBytes 8 (0 : UInt64).toBitVec.toInt ++ (z 8 ++ (z 8
    ++ (rb ++ (ws ++ (z 1 ++ (z 31 ++ (z 8 ++ (z 8 ++ z 8)))))))))))))))

def mem (rb ws : List UInt8) : DataMem := (block rb ws).At (0x10000 : BitVec 64)

def fs0 (rb ws : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x100b8, 0x10078, 64, 0, 0, 64, 0x10060, 0, 0, 0, 0, 0, 0, 0, 0x10020, 0⟩, zmms, flags, mem rb ws⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem fs_mem (rb ws : List UInt8) (hrb : rb.length = 32) (hws : ws.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    let s := fs0 rb ws zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 40 - BitVec.ofNat 64 0))
      ⋆ Eq ((z 24).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ bumpHeap 32
      ⋆ Eq (rb.At s.regs.rbx.toBitVec) ⋆ Eq (ws.At (s.regs.rbx.toBitVec + 32))
      ⋆ Eq ((z 1).At s.regs.rax.toBitVec) ⋆ Eq ((z 31).At (s.regs.rax.toBitVec + 1))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block rb ws).At (0x10000 : BitVec 64)) (mem rb ws) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length, hrb, hws])] at H
  simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, hrb, hws,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : (((Eq ((Int.toBytes 8 (65552#64).toInt).At 65540#64) ⋆ Eq ((z 32).At 65552#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64) ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65584#64)
        ⋆ Eq ((z 8).At 65592#64) ⋆ Eq ((z 24).At 65600#64) ⋆ Eq ((z 8).At 65624#64)
        ⋆ Eq ((Int.toBytes 8 (UInt64.toBitVec 0).toInt).At 65632#64) ⋆ Eq ((z 8).At 65640#64) ⋆ Eq ((z 8).At 65648#64)
        ⋆ Eq (rb.At 65656#64) ⋆ Eq (ws.At 65688#64) ⋆ Eq ((z 1).At 65720#64) ⋆ Eq ((z 31).At 65721#64)
        ⋆ Eq ((z 8).At 65752#64) ⋆ Eq ((z 8).At 65760#64) ⋆ Eq ((z 8).At 65768#64))) ⋆ Eq ((z 4).At 65548#64)) (mem rb ws) := by
    ecancel
  have H4 : ((bumpHeap 32 ⋆ _) ⋆ fun _ : DataMem => True) _ := sep_mono_left (fun _ => sep_mono_left (P' := bumpHeap 32) (fun m hm => ⟨65552#64, by decide, by rw [label_bump]; exact hm⟩)) (sep_true H2)
  rw [label_wb]
  simp only [s, fs0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H4 ⊢
  ac_nf at H4 ⊢

/-- **Non-vacuity of `fv_accept_main`.** In this host, from `fs0 rb ws`, the
real FixedVec.UnmarshalSSZ code returns nil. Every premise is proved here:
`MemmoveC` by `rt_memmove`, `MakesliceC` by `bump_makeslice`. -/
theorem fv_accept_runs (rb ws : List UInt8) (hrb : rb.length = 32) (hws : ws.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨fs0 rb ws zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (fv_accept_main 5 hk5 hf5 rb ws hrb hws (fs0 rb ws zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 1) (z 31) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] (z 24) rfl rfl bumpHeap 32 (fs_mem rb ws hrb hws zmms flags)
    (by simp [fs0]) (by simp [fs0]) rfl (by omega) (rt_memmove 97 hk97 hf97 0) (bump_makeslice 91 hk91 hf91 _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

end Fk.WitFv
