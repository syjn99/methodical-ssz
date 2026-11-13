import Codec.Kind.FixedBytesDecodeWindow
import Codec.CalleeDecodeWindow
import Codec.Kind.WindowSteps
import Codec.FixedBytesDecodePadding
import Prysm.Deposit_Data.DecodeFieldSegmentPadding
import Prysm.SyncCommitteeMessage.DecodeSegments
import Prysm.PendingConsolidation.DecodeAccept

/-!
# The earlier per-shape lemmas are instances of the window and step mechanisms: the `SyncCommitteeMessage` part

The declarations of the other types of this group are in `Codec/WindowStepsInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Prysm.SyncCommitteeMessage

open Codec

variable [Host]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- `Prysm.SyncCommitteeMessage.Decode.validator_index_arg` (hand set-up: the receiver is already in rax) from the step lemmas. -/
theorem Decode.validator_index_arg_inst : type_of% (@Prysm.SyncCommitteeMessage.Decode.validator_index_arg ‹Host›) := by
  intro k hk sp rcv bf aB aD aSrc aF hB' hD hSrc hF vD hvD R s hrsp hrax h_mem
  obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
  simp only at hrsp hrax h_mem ⊢
  subst rsp hSrc hF hrax
  apply step_load_value Reg64.rbx Reg64.rsp 120 _ (k + 82) (k + 83) (window_infix_at hk 82 1) (by rfl) (by rfl) sp aB bf hB' _ _ _ rfl (by ecancel)
  normalize_registers
  apply step_add_immediate Reg64.rbx 40 _ (k + 83) (k + 84) (window_infix_at hk 83 1) (by rfl) (by rfl)
  intro fl1; normalize_registers
  apply step_load_bytes Reg64.rdi Reg64.rsp 136 _ (k + 84) (k + 85) (window_infix_at hk 84 1) (by rfl) (by rfl) sp aD hD vD hvD _ _ _ rfl (by ecancel)
  normalize_registers
  apply step_add_immediate Reg64.rdi (-40) _ (k + 85) (k + 86) (window_infix_at hk 85 1) (by rfl) (by rfl)
  intro fl2; normalize_registers
  apply step_add_immediate Reg64.rax 40 _ (k + 86) (k + 87) (window_infix_at hk 86 1) (by rfl) (by rfl)
  intro fl3; normalize_registers
  apply step_move_immediate Reg64.rcx 8 _ (k + 87) (k + 88) (window_infix_at hk 87 1) (by rfl) (by rfl)
  normalize_registers
  apply Eventually.done
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | decide

end Prysm.SyncCommitteeMessage
