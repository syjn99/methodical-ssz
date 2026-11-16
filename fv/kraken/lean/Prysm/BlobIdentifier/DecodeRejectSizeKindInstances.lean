import Prysm.PendingPartialWithdrawal.DecodeRejectSize
import Prysm.AttestationData.DecodeRejectSize
import Codec.DecodeRejectSizeAnyFrame
import Prysm.Checkpoint.DecodeRejectSizeKindInstances

/-!
# Ties of `decodeRejectKindAnyFrame` to the committed size-reject theorems

The declared type of each committed theorem `Prysm.<Type>.Decode.reject_size` (9 flat development types and
AttestationData; the other types have the generated `Decode.generated_reject`, each with its own `_kind` line) is the kind instance; `with_reducible rfl` (the kind is an `abbrev` and the text is the same).
-/

open Machine Runtime

open Codec
