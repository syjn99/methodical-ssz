import Machine.Frame
import Codec.DecoderPrologue

/-!
# Lemmas for the field theorems of a generated accept proof

A generated field theorem is stated over the whole accept memory in entry-state terms (`Codec/Kind/DecodeAcceptAnyFrame.lean`).
Its proof uses the generated step chain of the field (`p2dec --gen4`) and these frame-parametric facts:
- `frame_j3`: the 24-byte spill area of the runtime calls is three 8-byte slots (a callee decoder spills its
  `rbx` into the middle one);
- `frame_lo8`: the low stack of a decoder with callee calls is `S` bytes and the callee's saved-`rbp` slot;
- `frame_lo`, `frame_lo0`: the low-stack address argument of a byte segment;
- `decepi_n`: the epilogue `add $F,%rsp; pop %rbp; retq` for any frame `F`.
They are the frame-parametric forms of the per-type hand lemmas `pd_j3`, `pd_lo8`, `pd_lo`, `e1_lo`, `pd_epi`.
-/

open Machine Runtime

namespace Codec

/-- Three 8-byte chunks at `x`, `x + 8`, `x + 16` are one 24-byte chunk at `x`. -/
theorem frame_j3 (x y z : BitVec 64) (a b c : List UInt8) (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hy : x + 8 = y) (hz : x + 16 = z) :
    Eq ((a ++ (b ++ c)).At x) = Eq (a.At x) ⋆ Eq (b.At y) ⋆ Eq (c.At z) := by
  subst hy hz
  rw [at_app _ _ (b := x + 8) (by rw [ha]; bv_omega) (by simp [ha, hb, hc]),
    at_app _ _ (b := x + 16) (by rw [hb]; bv_omega) (by simp [hb, hc])]
  simp only [Std.ExtHashMap.sep_assoc]

/-- The low stack of a decoder with callee calls: `S` bytes below the 8-byte slot at `y`. -/
theorem frame_lo8 (y : BitVec 64) (S : Nat) (hS : S < 2 ^ 60) (a f : List UInt8) (ha : a.length = S) (hf : f.length = 8) :
    Eq ((a ++ f).At (y - BitVec.ofNat 64 S)) = Eq (a.At (y - BitVec.ofNat 64 S)) ⋆ Eq (f.At y) := by
  refine at_app _ _ ?_ (by simp only [ha, hf]; omega)
  rw [ha]; bv_omega

/-- Low-stack address of a byte segment in a frame with callee calls (`S + 8` bytes below the return slot). -/
theorem frame_lo (x F B : BitVec 64) (S : Nat) (h : F + 16 = B) :
    x - F - 8 - BitVec.ofNat 64 (S + 8) = x - B - BitVec.ofNat 64 S := by
  subst h
  have : BitVec.ofNat 64 (S + 8) = BitVec.ofNat 64 S + 8 := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [this]; bv_omega

/-- Low-stack address of a byte segment in a frame without callee calls (`S` bytes below the return slot). -/
theorem frame_lo0 (x F B : BitVec 64) (S : Nat) (h : F + 8 = B) :
    x - F - 8 - BitVec.ofNat 64 S = x - B - BitVec.ofNat 64 S := by
  subst h
  generalize BitVec.ofNat 64 S = t
  bv_omega

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Epilogue, frame-parametric**: `add $F,%rsp` (window `q1` at `j`), then `pop %rbp; retq` (window `q2` at
`e`). With rsp = `sp`, the saved frame pointer `fp0` at `aFp = sp + F` and the return address `ra` at
`aRa = aFp + 8`: the pc is `ra`, rsp = `aRa + 8`, rbp = `fp0`; rax, rbx, r14 and the memory are kept. -/
theorem decepi_n (F : Int64) (q1 : Program) (j e : Nat) (hq1 : q1.IsInfixAt Host.prog j)
    (he1 : eraseNop q1 = [iAdd Reg64.rsp F]) (hend : j + q1.length = e)
    (q2 : Program) (hq2 : q2.IsInfixAt Host.prog e) (he2 : eraseNop q2 = decRet)
    (sp aFp aRa : BitVec 64) (hFp : sp + F.toBitVec = aFp) (hRa : aFp + 8 = aRa)
    (fp0 ra : UInt64) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 fp0.toBitVec.toInt).At aFp)
      ⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At aRa) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rax
        ∧ st.data.regs.rbx = s.regs.rbx ∧ st.data.regs.rsp = { toBitVec := aRa + 8 }
        ∧ st.data.regs.rbp = fp0 ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hFp hRa
  apply kstep_add Reg64.rsp F _ j e hq1 he1 hend
  intro fl; kn
  refine eventually_trans _ _ _ _ (decret_seg _ e hq2 he2 (sp + F.toBitVec) (sp + F.toBitVec + 8) rfl
    fp0 ra R _ (by rfl) (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrsp', hrbp', hreg, hmem⟩
  dsimp only at hpc hrsp' hrbp' hreg hmem
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp', ?_, hmem⟩
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rax (by decide) (by decide))
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.rbx (by decide) (by decide))
  · rw [hrsp']; exact congrArg UInt64.ofBitVec (by bv_omega)
  · exact UInt64.toBitVec_inj.mp (hreg Reg64.r14 (by decide) (by decide))

end Codec
