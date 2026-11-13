import Codec.Kind.CalleeDecode
import Codec.NopWindow

/-!
# The callee-decoder call block over a window (padding anywhere)

`calldec_seg_w` is `calldec_seg` (`Codec/CalleeDecode.lean`) with the dense template hypothesis replaced by a window:
`eraseNop q = callDec fn lok`. A `nop` may stand before the `callq`, between the `callq` and the `test`
(PendingConsolidation.TargetIndex, a field that the generator missed in the hold-out test of PendingConsolidation and SyncCommitteeMessage) or between `test` and `je`. `jc` is the index of the
`callq` (`j + nopPos q 0`): the return slot holds the address of directive `jc + 1`, which is the nop when
there is one. Callee specification: `U64CalleeAcc fn`, the existing form, unchanged. The entry registers
(rax = destination, rbx = source, rcx = 8) are fixed by the Go register ABI of that specification; the
set-up that establishes them is free (`Codec/WindowSteps.lean`).

`calldec_seg_dense`: the dense lemma `calldec_seg` is the instance `q := callDec fn lok` (statement equal).
-/

open Machine Runtime

open Codec
namespace Codec

variable [Host]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Call block of a callee-decoder field over a window**: the window `q` at `j` holds `callq fn; test
%rax,%rax; je lok` and nops; `lok:` at `j2`. Statement of `calldec_seg` with the return address
`addrOf (jc + 1)`, `jc` = the index of the `callq`. -/
theorem calldec_seg_w (fn lok : String) (q : Program) (j jc j2 : Nat)
    (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = callDec fn lok) (hjc : j + nopPos q 0 = jc)
    (hB : (callDecL lok).IsInfixAt Host.prog j2)
    (hl : label lok = Host.addrOf j2) (hC : U64CalleeAcc fn)
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
        (Eq ((Int.toBytes 8 (Host.addrOf (jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrbp hr14 hrax hrbx hrcx h_mem ⊢
  subst rsp rbp r14 rcx hRet hFp hS2 hrax hrbx hjc
  kwin hq
  kwat hq he callDec 0
  apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
  intro m1' H1
  simp only [Width.bytes, Width.bits] at H1
  kunfold
  try rw [show sp - 8#64 = sp - 8 from rfl] at *
  refine eventually_trans _ _ _ _ (hC _ (Host.addrOf (j + nopPos q 0 + 1)) e8 fp s2 c0 guard _
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
  kwnx hq he 0
  kwat hq he callDec 1
  intro _
  kwnx hq he 1
  kwat hq he callDec 2
  split
  case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
  simp only [Effects.All]
  rw [hl]
  kat hB callDecL 0
  apply Eventually.done
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by ecancel⟩

/-- The dense lemma `calldec_seg` is the instance of `calldec_seg_w` (same statement). -/
theorem calldec_seg_dense : type_of% (@calldec_seg ‹Host›) :=
  fun fn lok j j2 hA hB hl hC => calldec_seg_w fn lok _ j j j2 hA rfl rfl hB hl hC

set_option linter.unusedVariables false in
/-- Call-block statement kind over a window: start `k + j`, `callq` at `k + jc`, `lok:` at `k + j2`. -/
abbrev callDecSegKindWindow (C : Program) (fn lok : String) (j jc j2 : Nat) : Prop :=
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
        (Eq ((Int.toBytes 8 (Host.addrOf (k + jc + 1)).toBitVec.toInt).At aRet)
          ⋆ Eq ((Int.toBytes 8 rbp0.toBitVec.toInt).At aFp) ⋆ Eq ((Int.toBytes 8 src.toInt).At aS2)
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (r140.toBitVec + 16))
          ⋆ Eq (e8.At src) ⋆ Eq (e8.At dst) ⋆ F) st.data.dmem)
      ⟨s, Host.addrOf (k + j)⟩

/-- `callDecSegKindWindow` follows from `calldec_seg_w` and the window facts of an instance. -/
theorem callDecSegKindWindow_of (C : Program) (fn lok : String) (j jc j2 : Nat) (q : Program)
    (hq : ∀ k, C.IsInfixAt Host.prog k → q.IsInfixAt Host.prog (k + j)) (he : eraseNop q = callDec fn lok)
    (hjc : j + nopPos q 0 = jc)
    (hB : ∀ k, C.IsInfixAt Host.prog k → (callDecL lok).IsInfixAt Host.prog (k + j2))
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lok = Host.addrOf (k + j2)) :
    callDecSegKindWindow C fn lok j jc j2 :=
  fun k hk hf hC => calldec_seg_w fn lok q (k + j) (k + jc) (k + j2) (hq k hk) he (by omega) (hB k hk)
    (hl k hk hf) hC

/-- The dense kind `callDecSegKind` is the `jc = j` case of the window kind. -/
theorem callDecSegKind_eq_window (C : Program) (fn lok : String) (j j2 : Nat) :
    callDecSegKind C fn lok j j2 = callDecSegKindWindow C fn lok j j j2 := rfl

end Codec
