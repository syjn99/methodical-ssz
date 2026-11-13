import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Codec.Kind.WindowSteps
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.DecodeFieldSegmentPadding
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.PendingConsolidation.DecodeAccept
import Prysm.SyncCommitteeMessage.WindowStepsInstances

/-!
# The earlier per-shape lemmas are instances of the window and step mechanisms

Each theorem below has the TYPE of an earlier lemma (`type_of%`, so the statement is the committed one) and
is proved from the window and step lemmas only. No earlier proof is used.

* Window mechanism: `bytesdec_seg` (dense), `bytesdec_seg_optional_padding` (`pad` flag: the padding `nop`
  before `callq runtime.makeslice`), `Prysm.Deposit_Data.bytes32dec_seg_nop` (hand lemma), `Prysm.SyncCommitteeMessage.bytes32dec_seg_rax` (hand
  lemma, receiver in rax after the copy), `Prysm.PendingConsolidation.calldec_nop_seg` (hand lemma, `nop` after the callee call):
  each is `bytesdec_seg_window` / `calldec_seg_window` at one window (`q :=` the dense template; `he` by `rfl`).
* Step mechanism: the set-up lemmas `callarg_first_seg`, `callarg_reload_seg` (both with their `pad`
  flag), `callarg_lea_seg`, `callarg_mov_seg`, the two-directive read `u64dec_scratch_register_seg` at r8, and the hand
  set-up `Prysm.SyncCommitteeMessage.Decode.validator_index_arg`: each is a sequence of `kstep_*` applications.
(`calldec_seg` itself: `calldec_seg_dense` in `Codec/CalleeDecodeWindow.lean`.)
After the split of this module, the declarations of single types are in `Prysm/SyncCommitteeMessage/WindowStepsInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

open Codec

variable [Host]

/-- `bytesdec_seg` from the window lemma. -/
theorem bytesdec_seg_inst : type_of% (@bytesdec_seg ‹Host›) := by
  intro n hn lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl
  exact bytesdec_seg_window n hn Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    lff lwb dR dB dS fP fL fC src _ _ j1 j2 j2 (j2 + 6) (j2 + 12) hA rfl hB rfl rfl hl rfl rfl

/-- `bytesdec_seg_optional_padding` (`pad` flag) from the window lemma: the pad is a nop of the first window. -/
theorem bytesdec_seg_optional_padding_inst : type_of% (@bytesdec_seg_optional_padding ‹Host›) := by
  intro pad n hn lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl
  cases pad
  · exact bytesdec_seg_window n hn Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
      lff lwb dR dB dS fP fL fC src _ _ j1 j2 j2 (j2 + 6) (j2 + 12) hA rfl hB rfl rfl hl rfl rfl
  · exact bytesdec_seg_window n hn Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
      lff lwb dR dB dS fP fL fC src _ _ j1 j2 j2 (j2 + 6) (j2 + 12) hA rfl hB rfl rfl hl rfl rfl

/-- `Prysm.Deposit_Data.bytes32dec_seg_nop` (hand lemma) from the window lemma. -/
theorem bytes32dec_seg_nop_inst : type_of% (@Prysm.Deposit_Data.bytes32dec_seg_nop ‹Host›) := by
  intro lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl
  exact bytesdec_seg_window 32 (Or.inl rfl) Reg64.rdx Reg64.rdx (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl)))
    lff lwb dR dB dS fP fL fC src _ _ j1 j2 j2 (j2 + 6) (j2 + 12) hA rfl hB rfl rfl hl rfl rfl

/-- `Prysm.SyncCommitteeMessage.bytes32dec_seg_rax` (hand lemma) from the window lemma: `rY = rax`. -/
theorem bytes32dec_seg_rax_inst : type_of% (@Prysm.SyncCommitteeMessage.bytes32dec_seg_rax ‹Host›) := by
  intro lff lwb dR dB dS fP fL fC src j1 j2 hA hB hl
  exact bytesdec_seg_window 32 (Or.inl rfl) Reg64.rdx Reg64.rax (Or.inl rfl) (Or.inl rfl)
    lff lwb dR dB dS fP fL fC src _ _ j1 j2 j2 (j2 + 6) (j2 + 12) hA rfl hB rfl rfl hl rfl rfl

/-- `Prysm.PendingConsolidation.calldec_nop_seg` (hand lemma) from the window lemma: the nop is in the window. -/
theorem calldec_nop_seg_inst : type_of% (@Prysm.PendingConsolidation.calldec_nop_seg ‹Host›) := by
  intro fn lok j j2 hA hB hl hC
  exact calldec_seg_window fn lok _ j j j2 hA rfl rfl hB hl hC

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `callarg_first_seg` (`pad` flag) from the step lemmas. -/
theorem callarg_first_seg_inst : type_of% (@callarg_first_seg ‹Host›) := by
  intro pad f j hA rcv aF hF s hrax
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrax ⊢
  subst hrax hF
  cases pad
  · apply step_add_immediate Reg64.rax f _ j (j + 1) (window_infix_at hA 0 1) rfl rfl
    intro fl1; normalize_registers
    apply step_move_immediate Reg64.rcx 8 _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
    normalize_registers
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide
  · apply step_add_immediate Reg64.rax f _ j (j + 1) (window_infix_at hA 0 1) rfl rfl
    intro fl1; normalize_registers
    apply step_move_immediate Reg64.rcx 8 _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
    normalize_registers
    apply step_nops _ (j + 2) (j + 3) (window_infix_at hA 2 1) rfl rfl
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `callarg_reload_seg` (`pad` flag) from the step lemmas. -/
theorem callarg_reload_seg_inst : type_of% (@callarg_reload_seg ‹Host›) := by
  intro pad dB src dD c dR f j hA sp rcv bf aB aD aR aSrc aF hB' hD hR hSrc hF vD hvD R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hSrc hF
  cases pad
  · apply step_load_value Reg64.rbx Reg64.rsp dB _ j (j + 1) (window_infix_at hA 0 1) rfl rfl sp aB bf hB' _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rbx src _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
    intro fl1; normalize_registers
    apply step_load_bytes Reg64.rdi Reg64.rsp dD _ (j + 2) (j + 3) (window_infix_at hA 2 1) rfl rfl sp aD hD vD hvD _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rdi c _ (j + 3) (j + 4) (window_infix_at hA 3 1) rfl rfl
    intro fl2; normalize_registers
    apply step_load_value Reg64.rax Reg64.rsp dR _ (j + 4) (j + 5) (window_infix_at hA 4 1) rfl rfl sp aR rcv hR _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rax f _ (j + 5) (j + 6) (window_infix_at hA 5 1) rfl rfl
    intro fl3; normalize_registers
    apply step_move_immediate Reg64.rcx 8 _ (j + 6) (j + 7) (window_infix_at hA 6 1) rfl rfl
    normalize_registers
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide
  · apply step_load_value Reg64.rbx Reg64.rsp dB _ j (j + 1) (window_infix_at hA 0 1) rfl rfl sp aB bf hB' _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rbx src _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
    intro fl1; normalize_registers
    apply step_load_bytes Reg64.rdi Reg64.rsp dD _ (j + 2) (j + 3) (window_infix_at hA 2 1) rfl rfl sp aD hD vD hvD _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rdi c _ (j + 3) (j + 4) (window_infix_at hA 3 1) rfl rfl
    intro fl2; normalize_registers
    apply step_load_value Reg64.rax Reg64.rsp dR _ (j + 4) (j + 5) (window_infix_at hA 4 1) rfl rfl sp aR rcv hR _ _ _ rfl (by ecancel)
    normalize_registers
    apply step_add_immediate Reg64.rax f _ (j + 5) (j + 6) (window_infix_at hA 5 1) rfl rfl
    intro fl3; normalize_registers
    apply step_move_immediate Reg64.rcx 8 _ (j + 6) (j + 7) (window_infix_at hA 6 1) rfl rfl
    normalize_registers
    apply step_nops _ (j + 7) (j + 8) (window_infix_at hA 7 1) rfl rfl
    apply Eventually.done
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `callarg_lea_seg` from the step lemmas. -/
theorem callarg_lea_seg_inst : type_of% (@callarg_lea_seg ‹Host›) := by
  intro dB src dD c dR f j hA sp rcv bf aB aD aR aSrc aF hB' hD hR hSrc hF vD hvD R s hrsp h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp h_mem ⊢
  subst rsp hSrc hF
  apply step_load_value Reg64.rbx Reg64.rsp dB _ j (j + 1) (window_infix_at hA 0 1) rfl rfl sp aB bf hB' _ _ _ rfl (by ecancel)
  normalize_registers
  apply step_lea Reg64.rdx Reg64.rbx src _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
  normalize_registers
  apply step_load_bytes Reg64.rdi Reg64.rsp dD _ (j + 2) (j + 3) (window_infix_at hA 2 1) rfl rfl sp aD hD vD hvD _ _ _ rfl (by ecancel)
  normalize_registers
  apply step_add_immediate Reg64.rdi c _ (j + 3) (j + 4) (window_infix_at hA 3 1) rfl rfl
  intro fl1; normalize_registers
  apply step_load_value Reg64.rax Reg64.rsp dR _ (j + 4) (j + 5) (window_infix_at hA 4 1) rfl rfl sp aR rcv hR _ _ _ rfl (by ecancel)
  normalize_registers
  apply step_lea Reg64.rsi Reg64.rax f _ (j + 5) (j + 6) (window_infix_at hA 5 1) rfl rfl
  normalize_registers
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `callarg_mov_seg` from the step lemmas. -/
theorem callarg_mov_seg_inst : type_of% (@callarg_mov_seg ‹Host›) := by
  intro j hA s
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only
  apply step_move_register Reg64.rax Reg64.rsi _ j (j + 1) (window_infix_at hA 0 1) rfl rfl
  normalize_registers
  apply step_move_register Reg64.rbx Reg64.rdx _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl
  normalize_registers
  apply step_move_immediate Reg64.rcx 8 _ (j + 2) (j + 3) (window_infix_at hA 2 1) rfl rfl
  normalize_registers
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The two-directive inline uint64 read `u64dec_scratch_register_seg` at its development register r8, from the
load and store steps. The step lemmas hold for every base / scratch register. -/
theorem u64dec_scratch_register_seg_r8_inst (src f : Int64) (j : Nat)
    (hA : (u64DecScratchRegister Reg64.r8 src f).IsInfixAt Host.prog j)
    (bf rcv aSrc aF : BitVec 64) (hSrc : bf + src.toBitVec = aSrc) (hF : rcv + f.toBitVec = aF)
    (v vF : List UInt8) (hv : v.length = 8) (hvF : vF.length = 8)
    (R : DataMem → Prop)
    (s : MachineData) (hrbx : s.regs.rbx.toBitVec = bf) (hrax : s.regs.rax.toBitVec = rcv)
    (h_mem : s.dmem =⋆ Eq (v.At aSrc) ⋆ Eq (vF.At aF) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (j + 2) ∧ st.data.regs.rsp = s.regs.rsp
        ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14
        ∧ st.data.regs.rax = s.regs.rax ∧ st.data.regs.rbx = s.regs.rbx
        ∧ (∀ r : Reg64, r ≠ Reg64.r8 → st.data.regs.get64 r = s.regs.get64 r)
        ∧ (Eq (v.At aSrc) ⋆ Eq (v.At aF) ⋆ R) st.data.dmem)
      ⟨s, Host.addrOf j⟩ := by
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrbx hrax h_mem ⊢
  apply step_load_bytes Reg64.r8 Reg64.rbx src _ j (j + 1) (window_infix_at hA 0 1) rfl rfl bf aSrc hSrc v hv _ _ _ (by exact hrbx) (by ecancel)
  normalize_registers
  apply step_store Reg64.r8 Reg64.rax f _ (j + 1) (j + 2) (window_infix_at hA 1 1) rfl rfl rcv aF hF vF hvF _ _ _ (by exact hrax) (by ecancel)
  intro m' H
  normalize_registers
  simp only [Reg64s.get64, toBytes_ofInt_ofBytes 64 8 rfl v hv] at H
  apply Eventually.done
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, by ecancel⟩
  intro r hr
  cases r <;> first | rfl | exact absurd rfl hr

end Codec
