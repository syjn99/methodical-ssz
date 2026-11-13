import Codec.CalleeDecode
import Codec.InlineUint64RegisterBase

/-!
# Statement kinds of the callee-decoder call block, its argument set-ups and the two-directive
inline uint64 read

Each kind is the conclusion of its lemma (`Codec/CalleeDecode.lean`, `Codec/InlineUint64RegisterBase.lean`) with `j := k + j` (`j2 := k + j2`),
after the binders `k hk hf` (the idiom of `Codec/Kind/FieldPatterns.lean`). The `_of` theorems prove a kind from the lemma and
the code facts of an instance, so the kind body is kernel-checked against the lemma conclusion. The callee
specification `U64CalleeAcc fn` is a hypothesis of `callDecSegKind` (discharged at the composition by the
proved `Prysm.<Type>.Decode.accept_function_spec_holds` theorems). The scratch register of the uint64 read is in its kind, because it is in
the statement (the register clause).
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

set_option linter.unusedVariables false in
/-- Call-block statement kind: `callq fn; test; je lok` at `k + j`, `lok:` at `k + j2` of the decoder `C`, callee specification `U64CalleeAcc fn` as a hypothesis. -/
abbrev callDecSegKind (C : Program) (fn lok : String) (j j2 : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k) (hC : U64CalleeAcc fn)
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
      ⋆ Eq (e8.At src) ⋆ Eq (c0.At dst) ⋆ F),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j2 + 1) ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0
        ∧ st.data.regs.rsp = { toBitVec := sp } ∧ st.data.regs.rbp = rbp0 ∧ st.data.regs.r14 = r140 ∧
        (Eq ((Int.toBytes 8 (Host.addrOf (k + j + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callDecSegKind` follows from `calldec_seg` and the code facts of an instance. -/
theorem callDecSegKind_of (C : Program) (fn lok : String) (j j2 : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (callDec fn lok).IsInfixAt Host.prog (k + j))
    (hB : ∀ k, C.IsInfixAt Host.prog k → (callDecL lok).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lok = Host.addrOf (k + j2)) :
    callDecSegKind C fn lok j j2 :=
  fun k hk hf hC => calldec_seg fn lok (k + j) (k + j2) (hA k hk) (hB k hk) (hl k hk hf) hC

set_option linter.unusedVariables false in
/-- First-field set-up statement kind: `add $f,%rax; mov $0x8,%ecx` (+ `nop`) at `k + j`. -/
abbrev callArgFirstKind (C : Program) (pad : Bool) (f : Int64) (j : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (rcv aF : BitVec 64) (hF : rcv + f.toBitVec = aF)
    (s : MachineData) (hrax : s.regs.rax.toBitVec = rcv),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 2 + padLen pad) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧ st.data.regs.rbx = s.regs.rbx
        ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8 ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callArgFirstKind` follows from `callarg_first_seg` and the code facts of an instance. -/
theorem callArgFirstKind_of (C : Program) (pad : Bool) (f : Int64) (j : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (callArgFirst pad f).IsInfixAt Host.prog (k + j)) :
    callArgFirstKind C pad f j :=
  fun k hk _ => callarg_first_seg pad f (k + j) (hA k hk)

set_option linter.unusedVariables false in
/-- Reload set-up statement kind: 7 directives (+ `nop`) at `k + j`; `c` (the `add` to rdi) is not in the statement. -/
abbrev callArgReloadKind (C : Program) (pad : Bool) (dB src dD c dR f : Int64) (j : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hD : sp + dD.toBitVec = aD) (hR : sp + dR.toBitVec = aR)
    (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 7 + padLen pad) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = aSrc ∧ st.data.regs.rax.toBitVec = aF ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callArgReloadKind` follows from `callarg_reload_seg` and the code facts of an instance. -/
theorem callArgReloadKind_of (C : Program) (pad : Bool) (dB src dD c dR f : Int64) (j : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (callArgReload pad dB src dD c dR f).IsInfixAt Host.prog (k + j)) :
    callArgReloadKind C pad dB src dD c dR f j :=
  fun k hk _ => callarg_reload_seg pad dB src dD c dR f (k + j) (hA k hk)

set_option linter.unusedVariables false in
/-- `lea`-form set-up statement kind, first part: 6 directives at `k + j`; `c` is not in the statement. -/
abbrev callArgLeaKind (C : Program) (dB src dD c dR f : Int64) (j : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (sp rcv bf aB aD aR aSrc aF : BitVec 64)
    (hB' : sp + dB.toBitVec = aB) (hD : sp + dD.toBitVec = aD) (hR : sp + dR.toBitVec = aR)
    (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (vD : List UInt8) (hvD : vD.length = 8) (R : DataMem → Prop)
    (s : MachineData) (hrsp : s.regs.rsp = { toBitVec := sp })
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 bf.toInt).At aB) ⋆ Eq (vD.At aD)
      ⋆ Eq ((Int.toBytes 8 rcv.toInt).At aR) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 6) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rbx.toBitVec = bf ∧ st.data.regs.rdx.toBitVec = aSrc
        ∧ st.data.regs.rax.toBitVec = rcv ∧ st.data.regs.rsi.toBitVec = aF
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callArgLeaKind` follows from `callarg_lea_seg` and the code facts of an instance. -/
theorem callArgLeaKind_of (C : Program) (dB src dD c dR f : Int64) (j : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (callArgLea dB src dD c dR f).IsInfixAt Host.prog (k + j)) :
    callArgLeaKind C dB src dD c dR f j :=
  fun k hk _ => callarg_lea_seg dB src dD c dR f (k + j) (hA k hk)

set_option linter.unusedVariables false in
/-- `lea`-form set-up statement kind, second part: `mov %rsi,%rax; mov %rdx,%rbx; mov $0x8,%ecx` at `k + j`. -/
abbrev callArgMovKind (C : Program) (j : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (s : MachineData),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 3) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rsi ∧ st.data.regs.rbx = s.regs.rdx ∧ st.data.regs.rcx = 8
        ∧ st.data.dmem = s.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callArgMovKind` follows from `callarg_mov_seg` and the code facts of an instance. -/
theorem callArgMovKind_of (C : Program) (j : Nat)
    (hA : ∀ k, C.IsInfixAt Host.prog k → callArgMov.IsInfixAt Host.prog (k + j)) :
    callArgMovKind C j :=
  fun k hk _ => callarg_mov_seg (k + j) (hA k hk)

set_option linter.unusedVariables false in
/-- Two-directive inline uint64 decode statement kind: `mov src(%rbx),%rX; mov %rX,f(%rax)` at `k + j`. -/
abbrev u64DecRRSegKind (C : Program) (rX : Reg64) (src f : Int64) (j : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k)
    (bf rcv aSrc aF : BitVec 64) (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrbx : s.regs.rbx.toBitVec = bf) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R),
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + j + 2) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ (∀ r : Reg64, r ≠ rX → st.data.regs.get64 r = s.regs.get64 r)
        ∧ (Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `u64DecRRSegKind` follows from `u64dec_rr_seg` and the code facts of an instance. -/
theorem u64DecRRSegKind_of (C : Program) (rX : Reg64) (src f : Int64) (j : Nat) (hX : U64RRReg rX)
    (hA : ∀ k, C.IsInfixAt Host.prog k → (u64DecRR rX src f).IsInfixAt Host.prog (k + j)) :
    u64DecRRSegKind C rX src f j :=
  fun k hk _ => u64dec_rr_seg rX hX src f (k + j) (hA k hk)

end Codec
