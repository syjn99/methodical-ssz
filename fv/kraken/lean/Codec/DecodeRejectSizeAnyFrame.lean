import Codec.FieldFrame
import Prysm.Checkpoint.DecodeRejectSize

/-!
# Frame-parametric size reject of a container decoder, and its statement kind

The size-reject path is the same code in every flat decoder: the prologue with `jne lerr` taken, `lerr:`,
the two words of `ssz.ErrSize` into rax / rbx, `add $F,%rsp; pop %rbp; retq`. Only the frame `F`, the first
spill displacement `dB = F + 24`, the size `sz` and the labels differ.
- `decRejectKindN C sz`: the statement of the committed theorems `Prysm.<Type>.Decode.reject_size` with the code
  constant and the size replaced (ties: `Prysm/BlobIdentifier/DecodeRejectSizeKindInstances.lean`).
- `decrej_seg`: the proof over windows (nops anywhere): `decPro` (`Codec/DecoderPrologue.lean`), `decErrL`, then `decepi_n`.
Not covered: callee error returns (`fmt.errorf`), `morestack`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- The error block of the size check, first part: `lerr:`, then the two words of `ssz.ErrSize` into rax and
rbx. The epilogue `add $F,%rsp; pop %rbp; retq` follows (`decepi_n`). -/
def decErrL (lerr : String) : Program :=
  [Kraken.Directive.label lerr,
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none
         ((ConstExpr.label "ssz.ErrSize").sub ConstExpr.after_current_instruction)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some RegOrRip.rip) none
         (((ConstExpr.label "ssz.ErrSize").add (ConstExpr.int64 8)).sub ConstExpr.after_current_instruction))))))]

variable [Host]

set_option linter.unusedVariables false in
/-- **Size-reject statement kind of a container decoder**: with `len(buf) ≠ sz` the decoder returns the two
words `e0`, `e1` of `ssz.ErrSize`; the receiver and the input are not read (they are in `R`). The text is the
statement of the committed theorems `Prysm.<Type>.Decode.reject_size` with the code constant and the size replaced. -/
abbrev decRejectKindN (C : Program) (sz : UInt64) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ sz),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Size reject, frame-parametric**: the prologue window `q` at `j` (`decPro`, the `jne lerr` taken because
`rcx ≠ sz`), the error window `q2` at `j2` = `lerr` (`decErrL`), then `add $F,%rsp` (window `q3` at `j3`) and
`pop %rbp; retq` (window `q4` at `j4`). `dB = F + 24`: the first spill is the rbx home slot `rsp₀ + 16`. -/
theorem decrej_seg (fn l0 lmore lerr : String) (F dB sz : Int64) (q : Program) (j : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = decPro fn l0 lmore lerr F dB sz)
    (hdB : dB.toBitVec = F.toBitVec + 24)
    (q2 : Program) (j2 j3 : Nat) (hq2 : q2.IsInfixAt Host.prog j2) (he2 : eraseNop q2 = decErrL lerr)
    (hend2 : j2 + q2.length = j3) (hl : label lerr = Host.addrOf j2)
    (q3 : Program) (j4 : Nat) (hq3 : q3.IsInfixAt Host.prog j3) (he3 : eraseNop q3 = [iAdd Reg64.rsp F])
    (hend3 : j3 + q3.length = j4) (q4 : Program) (hq4 : q4.IsInfixAt Host.prog j4) (he4 : eraseNop q4 = decRet)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx ≠ { toBitVec := sz.toBitVec }) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [ElfData.PrysmTarget.sszErrSize_addr_eq] at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  kwin hq
  kwat hq he decPro 0
  kwnx hq he 0
  kwat hq he decPro 1
  kwnx hq he 1
  kwat hq he decPro 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq he 2
  kwat hq he decPro 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kwnx hq he 3
  kwat hq he decPro 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kwnx hq he 4
  kwat hq he decPro 5
  kwnx hq he 5
  kwat hq he decPro 6
  kwnx hq he 6
  kwat hq he decPro 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by rw [hdB]; bv_omega) (by ecancel) (by exact h2)
  intro m2' H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  kwnx hq he 7
  kwat hq he decPro 8
  kwnx hq he 8
  kwat hq he decPro 9
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen; apply UInt64.toBitVec_inj.mp
    first
      | exact BitVec.eq_of_sub_eq_zero h
      | (apply BitVec.eq_of_toNat_eq
         have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega)
      | bv_omega
  simp only [Effects.All]
  rw [hl]
  kwin hq2
  kwat hq2 he2 decErrL 0
  kwnx hq2 he2 0
  kwat hq2 he2 decErrL 1
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwnx hq2 he2 1
  kwat hq2 he2 decErrL 2
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kwend hq2 he2 2 hend2
  refine eventually_trans _ _ _ _ (decepi_n F q3 j3 j4 hq3 he3 hend3 q4 hq4 he4
    (rsp.toBitVec - 8 - F.toBitVec) (rsp.toBitVec - 8) rsp.toBitVec (by bv_omega) (by bv_omega) rbp ra _ _
    (by first
      | rfl
      | (apply UInt64.toBitVec_inj.mp; rfl)
      | (apply UInt64.toBitVec_inj.mp; bv_omega)
      | (apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_sub, UInt64.toBitVec_ofNat]; bv_omega))
    (by ecancel)) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, hrsp, hrbp, hr14, hmem⟩
  dsimp only at hpc hrax hrbx hrsp hrbp hr14 hmem
  try simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl] at hrax hrbx
  apply Eventually.done
  refine ⟨hpc, ?_, ?_, ?_, hrbp, hr14, ?_⟩
  · first
      | exact hrax
      | (rw [hrax]; done)
      | (rw [hrax]; rfl)
  · first
      | exact hrbx
      | (rw [hrbx]; done)
      | (rw [hrbx]; rfl)
  · rw [hrsp]; apply UInt64.toBitVec_inj.mp
    first
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; done)
      | (simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega)
  · dsimp only; rw [hmem]; ecancel

end Codec
