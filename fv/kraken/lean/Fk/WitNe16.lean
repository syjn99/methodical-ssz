import Fk.NeAccept
import Fk.BumpMore
import Fk.RtCopy
import Fk.WHost

/-!
# Premise witness of `ne_accept_main` (1b-fix X4)

Host: data labels, the real Nested.UnmarshalSSZ (index 5), Scalars.UnmarshalSSZ
and ListU64.UnmarshalSSZ (the callees), the bump `runtime.makeslice`
(8-byte elements) and the 24-byte bump `runtime.newobject`. The two function
specifications are not assumed: `ScUAccC` comes from `sc_uacc_holds` and
`LuUAccC` from `lu_uacc_holds` (with `bump_makeslice`) on the callee code in
the same host. For every A word, Scalars value and ListU64 value with at most
16 elements, `s0` meets every premise of `ne_accept_main` and the function
returns nil. This file: L with 16 elements (`WitNe0`, `WitNe1`, `WitNe16` cover empty, one, maximum).
-/

open Fk Fk.Code Fk.W Fv1

namespace Fk.WitNe16

def dataLabels : Program :=
  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]

def P : Program := dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ ++ BumpAlloc ++ BumpNew24

set_option maxRecDepth 100000 in
theorem P_len : P.length = 400 := by rfl

instance host : Host := mkHost P (by rw [P_len]; decide)

theorem prog_eq : Host.prog = P := rfl

theorem hk_target : NestedUnmarshalSSZ.IsInfixAt Host.prog 5 := by
  rw [prog_eq]; exact ⟨ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ ++ BumpAlloc ++ BumpNew24, by simp [P, dataLabels]⟩

set_option maxRecDepth 100000 in
theorem hk_fnSc : ScalarsUnmarshalSSZ.IsInfixAt Host.prog 162 := by
  rw [prog_eq]
  have h : (dataLabels ++ NestedUnmarshalSSZ).length = 162 := by
    simp only [List.length_append, show NestedUnmarshalSSZ.length = 157 from by rfl]; rfl
  exact ⟨ListU64UnmarshalSSZ ++ BumpAlloc ++ BumpNew24, by rw [show P = (dataLabels ++ NestedUnmarshalSSZ) ++ (ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ ++ BumpAlloc ++ BumpNew24) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩

set_option maxRecDepth 100000 in
theorem hk_fnLu : ListU64UnmarshalSSZ.IsInfixAt Host.prog 195 := by
  rw [prog_eq]
  have h : (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ).length = 195 := by
    simp only [List.length_append, show NestedUnmarshalSSZ.length = 157 from by rfl, show ScalarsUnmarshalSSZ.length = 33 from by rfl]; rfl
  exact ⟨BumpAlloc ++ BumpNew24, by rw [show P = (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ) ++ (ListU64UnmarshalSSZ ++ BumpAlloc ++ BumpNew24) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩

set_option maxRecDepth 100000 in
theorem hk_makeslice : BumpAlloc.IsInfixAt Host.prog 388 := by
  rw [prog_eq]
  have h : (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ).length = 388 := by
    simp only [List.length_append, show NestedUnmarshalSSZ.length = 157 from by rfl, show ScalarsUnmarshalSSZ.length = 33 from by rfl, show ListU64UnmarshalSSZ.length = 193 from by rfl]; rfl
  exact ⟨BumpNew24, by rw [show P = (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ) ++ (BumpAlloc ++ BumpNew24) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩

set_option maxRecDepth 100000 in
theorem hk_newobject : BumpNew24.IsInfixAt Host.prog 394 := by
  rw [prog_eq]
  have h : (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ ++ BumpAlloc).length = 394 := by
    simp only [List.length_append, show NestedUnmarshalSSZ.length = 157 from by rfl, show ScalarsUnmarshalSSZ.length = 33 from by rfl, show ListU64UnmarshalSSZ.length = 193 from by rfl, show BumpAlloc.length = 6 from by rfl]; rfl
  exact ⟨[], by rw [show P = (dataLabels ++ NestedUnmarshalSSZ ++ ScalarsUnmarshalSSZ ++ ListU64UnmarshalSSZ ++ BumpAlloc) ++ (BumpNew24 ++ []) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩

set_option maxRecDepth 100000 in
theorem hf_target : LabelsFresh NestedUnmarshalSSZ 5 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_fnSc : LabelsFresh ScalarsUnmarshalSSZ 162 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_fnLu : LabelsFresh ListU64UnmarshalSSZ 195 := labelsFresh_of (by rw [prog_eq]; decide)

set_option maxRecDepth 100000 in
theorem hf_makeslice : ∀ i < 388, Host.prog[i]? ≠ some (.label "runtime.makeslice") := by
  have hl : "runtime.makeslice" ∉ labs (P.take 388) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩

set_option maxRecDepth 100000 in
theorem hf_newobject : ∀ i < 394, Host.prog[i]? ≠ some (.label "runtime.newobject") := by
  have hl : "runtime.newobject" ∉ labs (P.take 394) := by decide
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

def block (a8 f0 f1 f2 f3 f4 lb : List UInt8) : List UInt8 :=
  [0, 0, 0, 0] ++ ((Int.toBytes 8 (0x1000c : BitVec 64).toInt) ++ ((z 176) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 144) ++ ((z 8) ++ ((z 16) ++ ((z 24) ++ ((z 8) ++ ((z 8) ++ ((z 32) ++ ((z 8) ++ ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ ((z 8) ++ (a8 ++ (f0 ++ (f1 ++ (f2 ++ (f3 ++ (f4 ++ ([28, 0, 0, 0] ++ ([4, 0, 0, 0] ++ (lb))))))))))))))))))))))))))))

def mem (a8 f0 f1 f2 f3 f4 lb : List UInt8) : DataMem := (block a8 f0 f1 f2 f3 f4 lb).At (0x10000 : BitVec 64)

def s0 (a8 f0 f1 f2 f3 f4 lb : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=
  ⟨⟨0x101e4, 0x101fc, 160, 0, 0, 160, 0x101bc, 0, 0, 0, 0, 0, 0, 0, 0x100ac, 0⟩, zmms, flags, mem a8 f0 f1 f2 f3 f4 lb⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem s_mem (a8 f0 f1 f2 f3 f4 lb : List UInt8) (ha8 : a8.length = 8) (h0 : f0.length = 1) (h1 : f1.length = 2) (h2 : f2.length = 4) (h3 : f3.length = 8) (h4 : f4.length = 1) (hlb : lb.length = 128) (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 a8 f0 f1 f2 f3 f4 lb zmms flags
    s.dmem =⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 32)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 48)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((z 144).At (s.regs.rsp.toBitVec - 104 - 144 - BitVec.ofNat 64 0))
      ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At (s.regs.r14.toBitVec + 16)) ⋆ bumpHeap 176
      ⋆ Eq (a8.At s.regs.rbx.toBitVec)
      ⋆ Eq (f0.At (s.regs.rbx.toBitVec + 8)) ⋆ Eq (f1.At (s.regs.rbx.toBitVec + 8 + 1))
      ⋆ Eq (f2.At (s.regs.rbx.toBitVec + 8 + 3)) ⋆ Eq (f3.At (s.regs.rbx.toBitVec + 8 + 7))
      ⋆ Eq (f4.At (s.regs.rbx.toBitVec + 8 + 15))
      ⋆ Eq ([28, 0, 0, 0].At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + 28)) ⋆ Eq (lb.At (s.regs.rbx.toBitVec + 28 + 4))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ fun _ => True := by
  intro s
  have H : Eq ((block a8 f0 f1 f2 f3 f4 lb).At (0x10000 : BitVec 64)) (mem a8 f0 f1 f2 f3 f4 lb) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, ha8, h0, h1, h2, h3, h4, hlb]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd, ha8, h0, h1, h2, h3, h4, hlb,
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : ((Eq ((Int.toBytes 8 (65548#64).toInt).At 65540#64) ⋆ Eq ((z 176).At 65548#64))
      ⋆ (Eq ([0, 0, 0, 0].At 65536#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65724#64)
        ⋆ Eq ((z 144).At 65732#64)
        ⋆ Eq ((z 8).At 65876#64)
        ⋆ Eq ((z 16).At 65884#64)
        ⋆ Eq ((z 24).At 65900#64)
        ⋆ Eq ((z 8).At 65924#64)
        ⋆ Eq ((z 8).At 65932#64)
        ⋆ Eq ((z 32).At 65940#64)
        ⋆ Eq ((z 8).At 65972#64)
        ⋆ Eq ((Int.toBytes 8 (0 : UInt64).toBitVec.toInt).At 65980#64)
        ⋆ Eq ((z 8).At 65988#64)
        ⋆ Eq ((z 8).At 65996#64)
        ⋆ Eq ((z 8).At 66004#64)
        ⋆ Eq ((z 8).At 66012#64)
        ⋆ Eq ((z 8).At 66020#64)
        ⋆ Eq ((z 8).At 66028#64)
        ⋆ Eq ((z 8).At 66036#64)
        ⋆ Eq (a8.At 66044#64)
        ⋆ Eq (f0.At 66052#64)
        ⋆ Eq (f1.At 66053#64)
        ⋆ Eq (f2.At 66055#64)
        ⋆ Eq (f3.At 66059#64)
        ⋆ Eq (f4.At 66067#64)
        ⋆ Eq ([28, 0, 0, 0].At 66068#64)
        ⋆ Eq ([4, 0, 0, 0].At 66072#64)
        ⋆ Eq (lb.At 66076#64))) (mem a8 f0 f1 f2 f3 f4 lb) := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap 176) (fun m hm => ⟨65548#64, by decide, by rw [label_bump]; exact hm⟩) H2
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  apply sep_true (F := Eq ((z 24).At 65900#64) ⋆ Eq ((z 32).At 65940#64))
  have hu0 : (UInt64.toBitVec 0) = 0#64 := rfl
  have huN : ∀ n : Nat, (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := fun _ => rfl
  simp only [hu0, huN] at H3 ⊢
  refine Eq.mp ?_ H3
  exact congrFun (by ac_rfl) _

/-- **Non-vacuity of `ne_accept_main`.** Every premise holds in this host: the
two `newobject` contracts by `bump_newobject24`, `ScUAccC` by `sc_uacc_holds`
and `LuUAccC` by `lu_uacc_holds` (callee code in the same host, its makeslice
by `bump_makeslice`). The function returns nil. -/
theorem ne_accept_runs (a8 : List UInt8) (sg : Scalars) (lg : ListU64) (ha8 : a8.length = 8)
    (hlen : lg.l.length = 16) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0)
      ⟨s0 a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
        zmms flags, Host.addrOf 5⟩ := by
  have hlg : lg.ok := by simp [ListU64.ok, hlen]
  exact eventually_mono (ne_accept_main 5 hk_target hf_target a8 ha8 sg lg hlg
    (s0 a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
      zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 144) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 (by decide) rfl rfl rfl rfl
    (fun _ => True) bumpHeap 176
    (s_mem a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
      ha8 (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size])
      (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size]) (by simp [scField])
      (by simp [u64Bytes_size, hlen]) zmms flags)
    (by simp [s0]) (by simp [s0]) (by simp [s0, hlen]) (by simp [s0]) (by simp [s0]) (by omega)
    (bump_newobject24 394 hk_newobject hf_newobject _) (bump_newobject24 394 hk_newobject hf_newobject _)
    (sc_uacc_holds 162 hk_fnSc hf_fnSc)
    (lu_uacc_holds 195 hk_fnLu hf_fnLu bumpHeap 0 (by decide) (bump_makeslice 388 hk_makeslice hf_makeslice _)))
    (fun _ h => ⟨h.1, h.2.1⟩)

end Fk.WitNe16
