import Fk.AdAccept
import Fk.BumpMore
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `ad_accept_main` (1b-fix X4)

Host: data labels, the real AttestationData.UnmarshalSSZ (index 5), the 1-byte
bump `runtime.makeslice` (`bump_makeslice1`), `RtCopy` (`rt_memmove`) and the
32-byte bump `runtime.newobject` (`bump_newobject32`), all on one bump heap of
160 bytes. For every 128-byte input, `s0` meets every premise of
`ad_accept_main` (eight calls, three contracts together) and the function
returns nil. AttestationData has a fixed size.
-/

open Fk Fk.Code Fk.W

namespace Fk.WitAd

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ PrysmAttestationDataUnmarshalSSZ ++ BumpAlloc1 ++ RtCopy ++ BumpNew32

set_option maxRecDepth 100000 in
theorem P_len : P.length = 229 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk_target : PrysmAttestationDataUnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨BumpAlloc1 ++ RtCopy ++ BumpNew32, by simp [P, dataLabels]⟩

set_option maxRecDepth 100000 in
theorem hk_makeslice : BumpAlloc1.IsInfixAt Host.prog 191 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmAttestationDataUnmarshalSSZ).length = 191 := by
    simp only [List.length_append, show PrysmAttestationDataUnmarshalSSZ.length = 186 from by rfl]; rfl
  exact ⟨RtCopy ++ BumpNew32, by rw [P, List.append_assoc, List.append_assoc, ← h, List.drop_left]⟩

set_option maxRecDepth 100000 in
theorem hk_rtcopy : RtCopy.IsInfixAt Host.prog 197 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmAttestationDataUnmarshalSSZ ++ BumpAlloc1).length = 197 := by
    simp only [List.length_append, show PrysmAttestationDataUnmarshalSSZ.length = 186 from by rfl, show BumpAlloc1.length = 6 from by rfl]; rfl
  exact ⟨BumpNew32, by rw [P, List.append_assoc, ← h, List.drop_left]⟩

set_option maxRecDepth 100000 in
theorem hk_newobject : BumpNew32.IsInfixAt Host.prog 223 := by
  rw [prog_eq]
  have h : (dataLabels ++ PrysmAttestationDataUnmarshalSSZ ++ BumpAlloc1 ++ RtCopy).length = 223 := by
    simp only [List.length_append, show PrysmAttestationDataUnmarshalSSZ.length = 186 from by rfl, show BumpAlloc1.length = 6 from by rfl, show RtCopy.length = 26 from by rfl]; rfl
  exact ⟨[], by rw [P, ← h, List.drop_left]; simp⟩

set_option maxRecDepth 100000 in
theorem hf_target : LabelsFresh PrysmAttestationDataUnmarshalSSZ 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_makeslice : ∀ i < 191, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 191) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

set_option maxRecDepth 100000 in
theorem hf_rtcopy : LabelsFresh RtCopy 197 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_newobject : ∀ i < 223, Host.prog[i]? ≠ some (.label "runtime.newobject") := by
  have hl : "runtime.newobject" ∉ labs (P.take 223) := by decide
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

def block (in0 in1 root se sroot te troot : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ ((Int.toBytes 8 (0x1000c : BitVec 64).toInt) ++ ((z 160) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ ((z 16) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ (in0 ++ (in1 ++ (root ++ (se ++ (sroot ++ (te ++ (troot ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8)))))))))))))))))))))))))))

def mem (in0 in1 root se sroot te troot : List UInt8) : DataMem := (block in0 in1 root se sroot te troot).At (0x10000 : BitVec 64)

def s0 (in0 in1 root se sroot te troot : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x10184, 0x10104, 128, 0, 0, 128, 0x100ec, 0, 0, 0, 0, 0, 0, 0, 0x1009c, 0⟩, zmms, flags, mem in0 in1 root se sroot te troot⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem s_mem (in0 in1 root se sroot te troot : List UInt8) (h0 : in0.length = 8) (h1 : in1.length = 8) (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32) (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 in0 in1 root se sroot te troot zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 56)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 56 - BitVec.ofNat 64 0))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 48)) ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ bumpHeap 160
      ⋆ Eq (in0.At s.regs.rbx.toBitVec) ⋆ Eq (in1.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (root.At (s.regs.rbx.toBitVec + 16)) ⋆ Eq (se.At (s.regs.rbx.toBitVec + 48))
      ⋆ Eq (sroot.At (s.regs.rbx.toBitVec + 56)) ⋆ Eq (te.At (s.regs.rbx.toBitVec + 88))
      ⋆ Eq (troot.At (s.regs.rbx.toBitVec + 96))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 32)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 48))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block in0 in1 root se sroot te troot).At (0x10000 : BitVec 64)) (mem in0 in1 root se sroot te troot) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length, h0, h1, hroot, hse, hsroot, hte, htroot])] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, h0, h1, hroot, hse, hsroot, hte, htroot,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : ((Eq ((Int.toBytes 8 (65548#64).toInt).At 65540#64) ⋆ Eq ((z 160).At 65548#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65708#64)
        ⋆ Eq ((z 8).At 65716#64)
        ⋆ Eq ((z 8).At 65724#64)
        ⋆ Eq ((z 16).At 65732#64)
        ⋆ Eq ((z 8).At 65748#64)
        ⋆ Eq ((z 8).At 65756#64)
        ⋆ Eq ((z 8).At 65764#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65772#64)
        ⋆ Eq ((z 8).At 65780#64)
        ⋆ Eq ((z 8).At 65788#64)
        ⋆ Eq (in0.At 65796#64)
        ⋆ Eq (in1.At 65804#64)
        ⋆ Eq (root.At 65812#64)
        ⋆ Eq (se.At 65844#64)
        ⋆ Eq (sroot.At 65852#64)
        ⋆ Eq (te.At 65884#64)
        ⋆ Eq (troot.At 65892#64)
        ⋆ Eq ((z 8).At 65924#64)
        ⋆ Eq ((z 8).At 65932#64)
        ⋆ Eq ((z 8).At 65940#64)
        ⋆ Eq ((z 8).At 65948#64)
        ⋆ Eq ((z 8).At 65956#64)
        ⋆ Eq ((z 8).At 65964#64)
        ⋆ Eq ((z 8).At 65972#64))) (mem in0 in1 root se sroot te troot) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 160) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  have H4 := sep_true (F := Std.ExtHashMap.emp) (by simpa only [Std.ExtHashMap.sep_emp] using H3)
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  generalize (fun _ : DataMem => True) = T at H4 ⊢
  ac_nf at H4 ⊢

/-- **Non-vacuity of `ad_accept_main`.** Every premise holds in this host: the
makeslice, memmove and newobject contracts by `bump_makeslice1`, `rt_memmove`
and `bump_newobject32` on one heap; the function returns nil. -/
theorem ad_accept_runs (in0 in1 root se sroot te troot : List UInt8) (h0 : in0.length = 8) (h1 : in1.length = 8) (hroot : root.length = 32)
    (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0)
      ⟨s0 in0 in1 root se sroot te troot zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (ad_accept_main 5 hk_target hf_target in0 in1 root se sroot te troot h0 h1 hroot hse hsroot hte htroot
    (s0 in0 in1 root se sroot te troot zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] (z 8) (z 16) rfl rfl rfl bumpHeap 160
    (s_mem in0 in1 root se sroot te troot h0 h1 hroot hse hsroot hte htroot zmms flags)
    (by simp [s0]) (by simp [s0]) rfl (by omega) (bump_makeslice1 191 hk_makeslice hf_makeslice _)
    (rt_memmove 197 hk_rtcopy hf_rtcopy 0) (bump_newobject32 223 hk_newobject hf_newobject _))
    (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

end Fk.WitAd
