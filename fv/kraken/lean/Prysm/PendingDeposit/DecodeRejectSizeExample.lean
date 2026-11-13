import Prysm.BlobIdentifier.DecodeRejectSizeKindInstances
import Prysm.PendingDeposit.GeneratedDecodeSteps
import Prysm.VoluntaryExit.DecodeRejectSizeExample

/-!
# Worked examples: size-reject theorems in generated style

`Decode.example_reject`: PendingDeposit (frame `0x40`), with the declared type of the committed hand theorem
`Decode.reject_size`. `Prysm.VoluntaryExit.Decode.example_reject`: VoluntaryExit (frame `0x48`), no hand theorem; statement =
`decodeRejectKindAnyFrame Prysm.VoluntaryExit.Code.unmarshalSSZ 16` (`_kind` line). Both are one application of `decode_reject_segment`; the generator reads
`F`, `dB`, `sz` and the directive indices of `lerr:`, `add`, `pop` from the `.S` file.
After the split of this module, the declarations of the other types are in `Prysm/VoluntaryExit/DecodeRejectSizeExample.lean`.
-/

open Machine Runtime Prysm.PendingDeposit.Code
variable [Host]

open Codec
namespace Prysm.PendingDeposit

set_option maxRecDepth 100000 in
/-- PendingDeposit: the committed size-reject statement, re-derived from `decode_reject_segment` (frame `0x40`). -/
theorem Decode.example_reject : type_of% (@Prysm.PendingDeposit.Decode.reject_size ‹Host›) := by
  intro k hk hf s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard hlen
  have hl := Machine.label_at' hk hf (j := 164)
    (by simp only [unmarshalSSZ, List.getElem?_cons_succ, List.getElem?_cons_zero]; rfl)
    (by simp only [unmarshalSSZ, List.take_succ_cons, List.take_zero, List.contains_cons, List.contains_nil]; decide)
  exact decode_reject_segment _ _ _ _ 64 88 192 _ k (window_infix_at hk 0 11) (by rfl) (by decide)
    _ (k + 164) (k + 167) (window_infix_at hk 164 3) (by rfl) (by rfl) hl
    _ (k + 168) (window_infix_at hk 167 1) (by rfl) (by rfl) _ (window_infix_at hk 168 2) (by rfl)
    s ra guard e0 e1 fp s2 hfp h2 R h_mem hguard (fun h => hlen (h.trans (by rfl)))

theorem Decode.example_reject_kind : ∀ (h : Host), type_of% (@Decode.example_reject h)
    = @Codec.decodeRejectKindAnyFrame h unmarshalSSZ 192 := by
  intro h; with_reducible rfl

end Prysm.PendingDeposit
