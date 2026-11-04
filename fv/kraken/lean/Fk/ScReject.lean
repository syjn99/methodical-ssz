import Fk.Step

/-!
# Scalars.UnmarshalSSZ, length reject path, on Kraken main (6064eec)

If `len(buf) != 16`, the function returns `ssz.ErrSize` (the two words at the
global) to the return address. Machine words, Go ABIInternal amd64: rax = c,
rbx = buf.ptr, rcx = len; error interface in (rax, rbx).

Hypotheses:
- the function occurs in the `Host` program at index `k`;
- `hL`: the label of the error block resolves to its directive (see `Fk.Labels`);
- memory: the return address at rsp, the spill slot at rsp+16, and the two words
  of the `ssz.ErrSize` global, all disjoint.
-/

open Fk Fk.Code
variable [Host]

theorem sc_reject_size_main (k : Nat) (hk : ScalarsUnmarshalSSZ.IsInfixAt Host.prog k)
    (hL : label "L_target.Scalars.UnmarshalSSZ_50" = Host.addrOf (k + 29))
    (s : MachineData) (ra e0 e1 : UInt64) (slot : List UInt8) (hsl : slot.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16#64))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec) ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hlen : s.regs.rcx ≠ 16) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1)
      ⟨s, Host.addrOf k⟩ := by
  have h0 := hk
  simp only [ScalarsUnmarshalSSZ] at h0
  -- 0: label
  apply estep h0
  simp [Directive.interp]
  -- 1: mov %rbx,0x10(%rsp)
  apply estep h0.cons.2
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at h_mem hlen ⊢
  have h_mem' : (Eq (slot.At (rsp.toBitVec + 16#64)) ⋆ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec) ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)) mem := by
    ecancel
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + 16#64) 8 slot _ mem ⟨h_mem', hsl⟩ rbx.toBitVec.toInt
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => exact hsl
  tactic =>
  simp only [Effects.All_require_write_access, Effects.All]
  -- 2: cmp $0x10,%rcx ; 3: jne
  apply estep h0.cons.2.cons.2
  sym =>
  kstep
  tactic =>
  apply estep h0.cons.2.cons.2.cons.2
  sym =>
  kstep
  tactic =>
  rename_i v status
  have hv : ¬ (v = 0#64) := by grind
  have hc : (!v == BitVec.zero 64) = true := by simpa using hv
  simp only [hc, ↓reduceIte, Effects.All]
  rw [hL]
  have h29 := isInfixAt_drop hk 29
  simp only [ScalarsUnmarshalSSZ, List.drop] at h29
  -- 29: label
  apply estep h29
  simp [Directive.interp]
  -- 30, 31: rip loads of ssz.ErrSize
  have hE0 : (Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec) ⋆
      (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16#64)) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R))
      (Mem.storeInt mem (rsp.toBitVec + 16#64) 8 rbx.toBitVec.toInt) := by ecancel
  apply estep h29.cons.2
  sym =>
  kstep
  case h_mem => tactic => simp [rip_addr']; exact hE0
  case h_len => exact Int.toBytes_length 8 _
  tactic =>
  simp only [Effects.All_require_read_access, Effects.All]
  have hE1 : (Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆
      (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16#64)) ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec)
        ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec) ⋆ R))
      (Mem.storeInt mem (rsp.toBitVec + 16#64) 8 rbx.toBitVec.toInt) := by ecancel
  apply estep h29.cons.2.cons.2
  simp only [Directive.interp, Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    AddrExpr.interp, ConstExpr.interp, Effects.All]
  simp only [Width.bits, Int.add_zero, rip_addr, BitVec.setWidth_eq]
  rw [load_sep _ _ _ _ _ _ hE1 (Int.toBytes_length 8 _)]
  simp only [Effects.All_require_read_access, MachineData.set, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Effects.All, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  -- 32: retq
  have hRA : (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At rsp.toBitVec) ⋆
      (Eq ((Int.toBytes 8 rbx.toBitVec.toInt).At (rsp.toBitVec + 16#64))
        ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At (label "ssz.ErrSize").toBitVec)
        ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R))
      (Mem.storeInt mem (rsp.toBitVec + 16#64) 8 rbx.toBitVec.toInt) := by ecancel
  apply estep h29.cons.2.cons.2.cons.2
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, Reg64s.get64]
  rw [load_sep _ _ _ _ _ _ hRA (Int.toBytes_length 8 _)]
  simp only [Effects.All_require_read_access, Effects.All, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact Eventually.done _ ⟨rfl, rfl, rfl⟩
