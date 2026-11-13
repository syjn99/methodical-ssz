import Machine.Step
import Machine.Labels
import Machine.Bytes
import Prysm.Checkpoint.DecodeRejectSize
import Prysm.ElfData.PrysmTarget
import Codec.Segment.Bytes32Loop

/-!
# Size reject of a fixed-size decoder, for ANY frame size `F` and ANY size `sz` (generalized once)

Go 1.26.10 compiles `if uint64(len(buf)) != sz { return ssz.ErrSize }` at the top of every fixed-size
`UnmarshalSSZ` to: guard check, `push %rbp; mov %rsp,%rbp; sub $F,%rsp; mov %rbx,F+24(%rsp)`, an optional `nop`,
`cmp $sz,%rcx; jne L_err`, and the error block `mov ssz.ErrSize, ssz.ErrSize+8; add $F,%rsp; pop %rbp; ret`.
The templates are the Kraken terms of `lv/link-hb` directives 0–10 and 30–35 with F, sz and the labels as
parameters. Proof text: `Prysm.SyncCommittee.Decode.reject_size` with the literal frame size replaced (address
equations by `bv_omega`) and the jne condition read for any `sz`. The fixed instances (SyncCommittee, HistoricalBatch) are re-derived in
`Codec/Segment/SizeRejectInstances.lean`.
-/

open Machine Runtime

namespace Codec.Segment

def rejHead (fnl l0 lmore : String) (F fB : Int64) : Program :=
  [Kraken.Directive.label fnl,
   Kraken.Directive.label l0,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rsp) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.r14)), idx := none, disp := ConstExpr.int64 16 })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.be) lmore)),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.push (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rbp) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rbp) (Width.W64))) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rsp) (Width.W64)))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.sub (RegOrMem.reg (Reg.low (Reg64.rsp) (Width.W64))) (Operand.imm (ConstExpr.int64 F)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.mem { base := some (RegOrRip.reg (Reg64.rsp)), idx := none, disp := ConstExpr.int64 fB }) (Operand.regOrMem (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W64))))))]

def rejCmp (sz : Int64) (lerr : String) : Program :=
  [Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.cmp (RegOrMem.reg (Reg.low (Reg64.rcx) (Width.W64))) (Operand.imm (ConstExpr.int64 sz)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.jcc (CondCode.nz) lerr))]

def rejErr (lerr : String) (F : Int64) : Program :=
  [Kraken.Directive.label lerr,
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rax) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.label "ssz.ErrSize") (ConstExpr.after_current_instruction) })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.mov (RegOrMem.reg (Reg.low (Reg64.rbx) (Width.W64))) (Operand.regOrMem (RegOrMem.mem { base := some (RegOrRip.rip), idx := none, disp := ConstExpr.sub (ConstExpr.add (ConstExpr.label "ssz.ErrSize") (ConstExpr.int64 8)) (ConstExpr.after_current_instruction) })))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.add (RegOrMem.reg (Reg.low (Reg64.rsp) (Width.W64))) (Operand.imm (ConstExpr.int64 F)))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.pop (RegOrMem.reg (Reg.low (Reg64.rbp) (Width.W64))))),
   Kraken.Directive.instr (Instr.regular (Width.W64) (Width.W64) (Operation.ret))]

variable [Host]

/-- **Size reject (machine), any frame and size**: `len(buf) ≠ sz`: the decoder returns the two words `e0`, `e1`
of `ssz.ErrSize`; the statement of `sc_reject_size_stmt` with the frame size `F` and the size `sz`. -/
theorem rej_size_g (F sz : Nat) (hF : F < 2 ^ 31) (hsz : sz < 2 ^ 31) (fnl l0 lmore lerr : String) (k jC jE : Nat)
    (hA : (rejHead fnl l0 lmore (OfNat.ofNat F) (OfNat.ofNat (F + 24))).IsInfixAt Host.prog k)
    (g : Glue (k + 8) jC) (hC : (rejCmp (OfNat.ofNat sz) lerr).IsInfixAt Host.prog jC)
    (hE : (rejErr lerr (OfNat.ofNat F)).IsInfixAt Host.prog jE) (hle : label lerr = Host.addrOf jE)
    (s : MachineData) (ra guard e0 e1 : UInt64) (fp s2 : List UInt8) (hfp : fp.length = 8) (h2 : s2.length = 8)
    (R : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
      ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx.toNat ≠ sz) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = e0 ∧ st.data.regs.rbx = e1
        ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 e0.toBitVec.toInt).At ElfData.PrysmTarget.sszErrSize_addr)
          ⋆ Eq ((Int.toBytes 8 e1.toBitVec.toInt).At (label "ssz.ErrSize" + 8).toBitVec) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only [ElfData.PrysmTarget.sszErrSize_addr_eq] at h_mem hguard hlen ⊢
  have := rsp.toNat_lt_size; have := guard.toNat_lt_size; have := rcx.toNat_lt_size; simp only [UInt64.size] at *
  have hFv : (OfNat.ofNat F : BitVec 64).toNat = F := by show (BitVec.ofNat 64 F).toNat = F; simp; omega
  kat hA rejHead 0
  kat hA rejHead 1
  kat hA rejHead 2
  apply load_step _ _ _ _ (Int.toBytes 8 guard.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hA rejHead 3
  split
  · rename_i h; exfalso
    simp [CondCode.interp, StatusFlags.from_result, BitVec.unsigned] at h
    rcases h with h | h
    · apply h; omega
    · have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this; omega
  simp only [Effects.All]
  kat hA rejHead 4
  apply store_step_at _ _ (rsp.toBitVec - 8) _ _ _ fp _ _ (by bv_omega) (by ecancel) (by exact hfp)
  intro m1 H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  kat hA rejHead 5
  kat hA rejHead 6
  kat hA rejHead 7
  apply store_step_at _ _ (rsp.toBitVec + 16) _ _ _ s2 _ _ (by bv_omega) (by ecancel) (by exact h2)
  intro m2 H2
  simp only [Width.bytes, Width.bits] at H2
  kunfold
  apply glue_nop g
  kat hC rejCmp 0
  kat hC rejCmp 1
  split
  case isFalse h =>
    exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    apply hlen
    have := congrArg BitVec.toNat h; simp [BitVec.toNat_sub] at this ⊢; omega
  simp only [Effects.All]
  rw [hle]
  kat hE rejErr 0
  kat hE rejErr 1
  apply load_step _ _ _ _ (Int.toBytes 8 e0.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hE rejErr 2
  apply load_step _ _ _ _ (Int.toBytes 8 e1.toBitVec.toInt) _ _ (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  kat hE rejErr 3
  kat hE rejErr 4
  apply load_step_at _ _ (rsp.toBitVec - 8) _ _ (Int.toBytes 8 rbp.toBitVec.toInt) _ _ (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub, hFv]; omega) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  kunfold
  kat hE rejErr 5
  apply load_step_at _ _ rsp.toBitVec _ _ (Int.toBytes 8 ra.toBitVec.toInt) _ _ (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub, hFv]; omega)
    (by ecancel) (by exact Int.toBytes_length 8 _)
  kunfold
  apply Eventually.done
  simp only [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_right
  · ecancel
  all_goals first
    | exact trivial
    | with_reducible rfl
    | (apply UInt64.toBitVec_inj.mp
       simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, Width.bits]
       done)
    | (apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, UInt64.toBitVec_add,
         UInt64.toBitVec_ofNat, Width.bits]
       omega)
    | (apply UInt64.toBitVec_inj.mp; apply BitVec.eq_of_toNat_eq
       simp [BitVec.toNat_add, BitVec.toNat_sub, hFv]
       omega)

end Codec.Segment
