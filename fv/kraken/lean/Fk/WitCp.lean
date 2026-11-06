import Fk.CpAccept
import Fk.RtCopy
import Fk.BumpMore
import Fk.WHost

/-!
# Premise witness of `cp_accept_main`

Host: data labels, the real Checkpoint.UnmarshalSSZ (index 5), the 1-byte bump
`runtime.makeslice` (index 77, `bump_makeslice1`) and `RtCopy` (index 83,
`rt_memmove`). For every epoch word `e8` and root (32 bytes), `cs0` meets every
premise of `cp_accept_main` and the function returns nil. Checkpoint has a
fixed size.
-/

open Fk Fk.Code Fk.W

namespace Fk.WitCp

set_option maxRecDepth 100000

set_option maxRecDepth 100000

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ PrysmCheckpointUnmarshalSSZ ++ BumpAlloc1 ++ RtCopy

theorem P_len : P.length = 109 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk5 : PrysmCheckpointUnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc1 ++ RtCopy, by simp [P, dataLabels]⟩

theorem hk77 : BumpAlloc1.IsInfixAt Host.prog 77 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmCheckpointUnmarshalSSZ).length = 77 := by
    rw [List.length_append, show PrysmCheckpointUnmarshalSSZ.length = 72 from by rfl]; rfl
  exact ⟨RtCopy, by rw [P, List.append_assoc, ← h, List.drop_left]⟩

theorem hk83 : RtCopy.IsInfixAt Host.prog 83 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmCheckpointUnmarshalSSZ ++ BumpAlloc1).length = 83 := by
    rw [List.length_append, List.length_append, show PrysmCheckpointUnmarshalSSZ.length = 72 from by rfl]; rfl
  exact ⟨[], by rw [P, ← h, List.drop_left]; simp⟩

theorem hf5 : LabelsFresh PrysmCheckpointUnmarshalSSZ 5 := labelsFresh_of (by rw [prog_eq]; decide)

theorem hf83 : LabelsFresh RtCopy 83 := labelsFresh_of (by rw [prog_eq]; decide)

theorem hf77 : ∀ i < 77, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 77) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

theorem label_wb : label "runtime.writeBarrier" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem label_bump : label "runtime.fvBump" = 0x10004 :=
  mk_label P _ 4 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

def block (e8 root : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ ((Int.toBytes 8 (0x10010 : BitVec 64).toInt) ++ (((z 4) ++ (z 32)) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 24) ++ ((z 8) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ (e8 ++ (root ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8)))))))))))))))))

def mem (e8 root : List UInt8) : DataMem := (block e8 root).At (0x10000 : BitVec 64)

def cs0 (e8 root : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x100a8, 0x10080, 40, 0, 0, 40, 0x10068, 0, 0, 0, 0, 0, 0, 0, 0x10020, 0⟩, zmms, flags, mem e8 root⟩

set_option maxHeartbeats 4000000 in
theorem cs_mem (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    let s := cs0 e8 root zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 48)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 0))
      ⋆ Eq ((z 24).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ bumpHeap 32
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block e8 root).At (0x10000 : BitVec 64)) (mem e8 root) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length, he8, hroot])] at H
  simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, he8, hroot,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : (((Eq ((Int.toBytes 8 (65552#64).toInt).At 65540#64) ⋆ Eq ((z 32).At 65552#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65584#64)
        ⋆ Eq ((z 8).At 65592#64)
        ⋆ Eq ((z 24).At 65600#64)
        ⋆ Eq ((z 8).At 65624#64)
        ⋆ Eq ((z 8).At 65632#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65640#64)
        ⋆ Eq ((z 8).At 65648#64)
        ⋆ Eq ((z 8).At 65656#64)
        ⋆ Eq (e8.At 65664#64)
        ⋆ Eq (root.At 65672#64)
        ⋆ Eq ((z 8).At 65704#64)
        ⋆ Eq ((z 8).At 65712#64)
        ⋆ Eq ((z 8).At 65720#64)
        ⋆ Eq ((z 8).At 65728#64))) ⋆ Eq ((z 4).At 65548#64)) (mem e8 root) := by
    ecancel
  have H4 : ((bumpHeap 32 ⋆ _) ⋆ fun _ : DataMem => True) _ := sep_mono_left (fun _ => sep_mono_left (P' := bumpHeap 32) (fun m hm => ⟨65552#64, by decide, by rw [label_bump]; exact hm⟩)) (sep_true H2)
  rw [label_wb]
  simp only [s, cs0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H4 ⊢
  ac_nf at H4 ⊢

/-- **Non-vacuity of `cp_accept_main`.** Every premise holds in this host, the
two contracts by `bump_makeslice1` and `rt_memmove`; the function returns nil. -/
theorem cp_accept_runs (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨cs0 e8 root zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (cp_accept_main 5 hk5 hf5 e8 root he8 hroot (cs0 e8 root zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] (z 24) rfl rfl bumpHeap 32 (cs_mem e8 root he8 hroot zmms flags)
    (by simp [cs0]) (by simp [cs0]) rfl (by omega) (bump_makeslice1 77 hk77 hf77 _) (rt_memmove 83 hk83 hf83 0))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

end Fk.WitCp
