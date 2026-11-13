import Codec.Bytes32Decode
import Prysm.ValidatorIndex.DecodeAcceptFunctionSpec
import Prysm.Epoch.DecodeAccept
import Prysm.Slot.DecodeAccept

/-!
# A field decoded by a call to another type's `UnmarshalSSZ` (uint64 overlay callee)

Added after the frozen generator ran on the hold-out types Deposit_Data and PendingPartialWithdrawal: the generator did not cover the fields that a callee
decodes. Go 1.26.10 compiles
`if err = x.F.UnmarshalSSZ(buf[s:s+8]); err != nil { ... }` for an overlay type of `uint64` (Slot,
CommitteeIndex, ValidatorIndex, Epoch) to an argument set-up, then

    callq <callee>.UnmarshalSSZ
    test %rax,%rax
    je L            -- nil error: continue at L

`U64CalleeAccept fn` is the text of the four existing function specifications `Prysm.Slot.Decode.accept_function_spec`, `Prysm.CommitteeIndex.Decode.accept_function_spec`,
`Prysm.ValidatorIndex.Decode.accept_function_spec`, `Prysm.Epoch.Decode.accept_function_spec` with the callee label as a parameter. It is the existing spec-hypothesis
form (`Prysm/Slot/CalleeDecodeFunctionSpecs.lean`: each existing spec is `U64CalleeAccept <its label>` by `rfl`); the proved theorems
`Prysm.Slot.Decode.accept_function_spec_holds`, `Prysm.CommitteeIndex.Decode.accept_function_spec_holds`, `Prysm.ValidatorIndex.Decode.accept_function_spec_holds`, `Prysm.Epoch.Decode.accept_function_spec_holds` discharge it. No runtime contract is used.

* `calldec_seg` — the reusable call block: `callDec fn lok` (3 directives) and the label `lok`.
* Argument set-up, the three straight-line forms of the seven development sites (register hand-over only,
  memory unchanged): `callarg_first_seg` (`add $f,%rax; mov $8,%ecx`), `callarg_reload_seg` (three reloads
  from the spills with `add`), `callarg_lea_seg` + `callarg_mov_seg` (the `lea` form whose results are moved
  to rax / rbx after an interleaved field read). `pad = true` adds the compiler padding `nop` before the call.
Not covered: any other register choice; pointer-field callees (`Prysm.Checkpoint.Decode.accept_function_spec`, a different specification form).
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

/-- Accept-path function specification of a `uint64`-overlay `UnmarshalSSZ` at the label `fn`
(`len(buf) = 8`): the common text of `Prysm.Slot.Decode.accept_function_spec`, `Prysm.CommitteeIndex.Decode.accept_function_spec`,
`Prysm.ValidatorIndex.Decode.accept_function_spec`, `Prysm.Epoch.Decode.accept_function_spec`. -/
def U64CalleeAccept (fn : String) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (e8 fp s2 c0 : List UInt8) (guard : UInt64) (F : DataMem → Prop),
    e8.length = 8 → fp.length = 8 → s2.length = 8 → c0.length = 8 →
    st.regs.rcx = 8 → guard.toNat < st.regs.rsp.toNat →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (c0.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.r14 = st.regs.r14
        ∧ (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label fn⟩

/-- Number of padding directives. -/
def padLen : Bool → Nat
  | false => 0
  | true => 1

/-- The call block: `callq fn; test %rax,%rax; je lok`. -/
def callDec (fn lok : String) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.call (RelRegOrMem.rel ((ConstExpr.label fn).sub ConstExpr.after_current_instruction)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.test (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rax Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.jcc CondCode.z lok))]

/-- The continuation label of the call block. -/
def callDecContinuationLabel (lok : String) : Program := [Kraken.Directive.label lok]

/-- Set-up of the first field: `add $f,%rax; mov $0x8,%ecx` (+ `nop`). -/
def callArgFirst : Bool → Int64 → Program
  | false, f =>
    [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rax Width.W64)) (Operand.imm (ConstExpr.int64 f)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 8))))]
  | true, f =>
    [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rax Width.W64)) (Operand.imm (ConstExpr.int64 f)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 8)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1))]

/-- Set-up by reload: `mov dB(%rsp),%rbx; add $src,%rbx; mov dD(%rsp),%rdi; add $c,%rdi; mov dR(%rsp),%rax;
add $f,%rax; mov $0x8,%ecx` (+ `nop`). -/
def callArgReload : Bool → Int64 → Int64 → Int64 → Int64 → Int64 → Int64 → Program
  | false, dB, src, dD, c, dR, f =>
    [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)) (Operand.imm (ConstExpr.int64 src)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dD)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rdi Width.W64)) (Operand.imm (ConstExpr.int64 c)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rax Width.W64)) (Operand.imm (ConstExpr.int64 f)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 8))))]
  | true, dB, src, dD, c, dR, f =>
    [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rbx Width.W64)) (Operand.imm (ConstExpr.int64 src)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dD)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rdi Width.W64)) (Operand.imm (ConstExpr.int64 c)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
         (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
       (Operation.add (RegOrMem.reg (Reg.low Reg64.rax Width.W64)) (Operand.imm (ConstExpr.int64 f)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
       (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 8)))),
     Kraken.Directive.instr (Instr.regular Width.W64 Width.W64 (Operation.nop 1))]

/-- Set-up, `lea` form, first part: `mov dB(%rsp),%rbx; lea src(%rbx),%rdx; mov dD(%rsp),%rdi; add $c,%rdi;
mov dR(%rsp),%rax; lea f(%rax),%rsi`. -/
def callArgLea (dB src dD c dR f : Int64) : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dB)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rdx Width.W64)
       (AddrExpr.mk (some (RegOrRip.reg Reg64.rbx)) none (ConstExpr.int64 src)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rdi Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dD)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.add (RegOrMem.reg (Reg.low Reg64.rdi Width.W64)) (Operand.imm (ConstExpr.int64 c)))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.mem (AddrExpr.mk (some (RegOrRip.reg Reg64.rsp)) none (ConstExpr.int64 dR)))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.lea (Reg.low Reg64.rsi Width.W64)
       (AddrExpr.mk (some (RegOrRip.reg Reg64.rax)) none (ConstExpr.int64 f))))]

/-- Set-up, `lea` form, second part: `mov %rsi,%rax; mov %rdx,%rbx; mov $0x8,%ecx`. -/
def callArgMov : Program :=
  [Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rax Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rsi Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W64
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rbx Width.W64))
       (Operand.regOrMem (RegOrMem.reg (Reg.low Reg64.rdx Width.W64))))),
   Kraken.Directive.instr (Instr.regular Width.W64 Width.W32
     (Operation.mov (RegOrMem.reg (Reg.low Reg64.rcx Width.W32)) (Operand.imm (ConstExpr.int64 8))))]

/-- Closing step of the set-up lemmas: register equations. -/
local macro "call_argument_close" : tactic => `(tactic| (
  all_goals first
    | rfl
    | exact BitVec.add_comm _ _
    | (apply BitVec.eq_of_toNat_eq
       simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat, UInt64.toNat_toBitVec,
         UInt64.toBitVec_add, UInt64.toBitVec_ofNat, Width.bits, Nat.reducePow, Nat.add_comm]
       done)))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Call block of a callee-decoder field**: `callq fn; test %rax,%rax; je lok` at `j`, `lok:` at `j2`.
With rsp = `sp`, rcx = 8, the destination `dst` in rax and the source `src` in rbx, the callee (specification
`hC`) stores the 8 source bytes `e8` at `dst` and returns nil; the block ends after the label `lok` with
rax = rbx = 0. The return slot `aRet = sp − 8` holds the address of directive `j + 1`, the callee's frame
pointer slot `aFp = sp − 16` the caller's rbp and its spill slot `aS2 = sp + 8` the source pointer. -/
theorem calldec_seg (fn lok : String) (j j2 : Nat)
    (hA : (callDec fn lok).IsInfixAt Host.prog j) (hB : (callDecContinuationLabel lok).IsInfixAt Host.prog j2)
    (hl : label lok = Host.addrOf j2) (hC : U64CalleeAccept fn)
    (sp dst src aRet aFp aS2 : BitVec 64)
    (hRet : sp - 8 = aRet) (hFp : sp - 16 = aFp) (hS2 : sp + 8 = aS2)
    (rbp0 r140 guard : UInt64) (e8 rslot fp s2 c0 : List UInt8)
    (he8 : e8.length = 8) (hrs : rslot.length = 8) (hfp : fp.length = 8) (hs2 : s2.length = 8)
    (hc0 : c0.length = 8) (hguard : guard.toNat < aRet.toNat)
    (F : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp }) (hrbp : s.regs.rbp = rbp0)
    (hr14 : s.regs.r14 = r140) (hrax : s.regs.rax.toBitVec = dst) (hrbx : s.regs.rbx.toBitVec = src)
    (hrcx : s.regs.rcx = 8)
    (h_mem : s.dmem =⋆ Eq (rslot.At aRet) ⋆ Eq (fp.At aFp) ⋆ Eq (s2.At aS2)
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j2 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (j + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx h_mem ⊢
  subst rsp rbp r14 rcx hRet hFp hS2 hrax hrbx
  step_directive hA callDec 0
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  unfold_step
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hC _ (Host.addrOf (j + 0 + 1)) e8 fp s2 c0 guard _
    he8 hfp hs2 hc0 rfl hguard
    (by dsimp only; rw [show sp - 8 - 8 = sp - 16 by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega]; ecancel)) ?_
  rintro ⟨d2, pc2⟩ ⟨hpc2, hrax2, hrbx2, hrsp2, hrbp2, hr142, Hm2⟩
  dsimp only at hpc2 hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  subst hpc2
  obtain ⟨⟨rax2, rbx2, rcx2, rdx2, rsi2, rdi2, rsp2, rbp2, r82, r92, r102, r112, r122, r132, r142, r152⟩,
    zmms2, flags2, mem2⟩ := d2
  simp only at hrax2 hrbx2 hrsp2 hrbp2 hr142 Hm2
  rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
    apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp2
  subst rax2 rbx2 rsp2 rbp2 r142
  rw [show sp - 8 - 8 = sp - 16 by bv_omega, show sp - 8 + 16 = sp + 8 by bv_omega] at Hm2
  rw [show j + 0 + 1 = j + 1 from rfl] at Hm2
  step_directive hA callDec 1
  intro _
  step_directive hA callDec 2
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  step_directive hB callDecContinuationLabel 0
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by ecancel⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Set-up of the first callee field**: `add $f,%rax; mov $0x8,%ecx` (+ `nop` if `pad`) at `j`. With the
receiver `rcv` in rax: rax = `aF = rcv + f`, rcx = 8; rbx, rsp, rbp, r14 and the memory are unchanged. -/
theorem callarg_first_seg (pad : Bool) (f : Int64) (j : Nat)
    (hA : (callArgFirst pad f).IsInfixAt Host.prog j)
    (rcv aF : BitVec 64) (hF : rcv + f.toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 2 + padLen pad) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax ⊢
  subst hrax hF
  cases pad
  · step_directive hA callArgFirst 0
    step_directive hA callArgFirst 1
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    call_argument_close
  · step_directive hA callArgFirst 0
    step_directive hA callArgFirst 1
    step_directive hA callArgFirst 2
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    call_argument_close

set_option hygiene false in
/-- Steps 0–6 of `callArgReload` (binders of the lemma below). -/
local macro "call_argument_reload_steps" : tactic => `(tactic| (
  step_directive hA callArgReload 0
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA callArgReload 1
  step_directive hA callArgReload 2
  apply load_step_at _ _ aD _ _ vD _ _ (by rw [← hD]) (by ecancel) (by exact hvD)
  unfold_step
  step_directive hA callArgReload 3
  step_directive hA callArgReload 4
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA callArgReload 5
  step_directive hA callArgReload 6))

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Set-up of a callee field by reload**: 7 directives (+ `nop` if `pad`) at `j`. With rsp = `sp`, the
buffer pointer `bf` in the spill slot `aB = sp + dB`, 8 bytes `vD` in `aD = sp + dD` and the receiver `rcv`
in `aR = sp + dR`: rbx = `aSrc = bf + src`, rax = `aF = rcv + f`, rcx = 8; rsp, rbp, r14 and the memory are
unchanged. -/
theorem callarg_reload_seg (pad : Bool) (dB src dD c dR f : Int64) (j : Nat)
    (hA : (callArgReload pad dB src dD c dR f).IsInfixAt Host.prog j)
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hD : sp + dD.toBitVec = aD) (hR : sp + dR.toBitVec = aR)
    (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 7 + padLen pad) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hSrc hF
  cases pad
  · call_argument_reload_steps
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    call_argument_close
  · call_argument_reload_steps
    step_directive hA callArgReload 7
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    call_argument_close

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Set-up of a callee field, `lea` form, first part**: 6 directives at `j`. With rsp = `sp` and the spill
slots as in `callarg_reload_seg`: rbx = `bf`, rdx = `aSrc = bf + src`, rax = `rcv`, rsi = `aF = rcv + f`;
rsp, rbp, r14 and the memory are unchanged. -/
theorem callarg_lea_seg (dB src dD c dR f : Int64) (j : Nat)
    (hA : (callArgLea dB src dD c dR f).IsInfixAt Host.prog j)
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hD : sp + dD.toBitVec = aD) (hR : sp + dR.toBitVec = aR)
    (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 6) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = bf ∧ st.data.regs.rdx.toBitVec = aSrc
        ∧ st.data.regs.rax.toBitVec = rcv ∧ st.data.regs.rsi.toBitVec = aF
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hSrc hF
  step_directive hA callArgLea 0
  apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA callArgLea 1
  step_directive hA callArgLea 2
  apply load_step_at _ _ aD _ _ vD _ _ (by rw [← hD]) (by ecancel) (by exact hvD)
  unfold_step
  step_directive hA callArgLea 3
  step_directive hA callArgLea 4
  apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
    (by exact Int.toBytes_length 8 _)
  unfold_step
  step_directive hA callArgLea 5
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  call_argument_close

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- **Set-up of a callee field, `lea` form, second part**: `mov %rsi,%rax; mov %rdx,%rbx; mov $0x8,%ecx`
at `j`: rax = old rsi, rbx = old rdx, rcx = 8; rsp, rbp, r14 and the memory are unchanged. -/
theorem callarg_mov_seg (j : Nat) (hA : callArgMov.IsInfixAt Host.prog j) (s : MachineData) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 3) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rsi ∧ st.data.regs.rbx = s.regs.rdx ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only
  step_directive hA callArgMov 0
  step_directive hA callArgMov 1
  step_directive hA callArgMov 2
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  call_argument_close

end Codec
