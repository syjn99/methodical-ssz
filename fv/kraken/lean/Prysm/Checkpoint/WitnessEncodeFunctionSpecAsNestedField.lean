import Prysm.Checkpoint.FunctionSpecsAsNestedField
import Prysm.Checkpoint.WitnessEncodeFastPath

/-!
# `Encode.fast_path_function_spec` holds on a concrete host

On the Checkpoint witness hosts of `Prysm.Checkpoint.WitnessDecodeAccept` (decoder, Epoch decoder, bump makeslice model,
memmove model) and `Prysm.Checkpoint.WitnessEncodeFastPath` (encoder, memmove model), the function specifications hold:
their hypotheses (`MakesliceContract`, `MemmoveContract`) are discharged by the runtime models. Together with the
witnesses `cp_accept_runs` / `cpm_runs_*` (which run the code on concrete states) this shows the
specifications are not vacuous. `*_spec_here` shows that the specification holds as an
instance on this host; it does not by itself show that the premises of a main theorem are satisfiable. That
(non-vacuity) comes from the run witnesses.
-/

open Machine Runtime Machine.Witness Prysm.Checkpoint.Code

namespace Prysm.Checkpoint.Witness.EncodeFunctionSpecAsNestedField

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem runs_function_spec : @Encode.fast_path_function_spec Prysm.Checkpoint.Witness.EncodeFastPath.host 0 :=
  @Encode.fast_path_function_spec_holds Prysm.Checkpoint.Witness.EncodeFastPath.host 0 Prysm.Checkpoint.Witness.EncodeFastPath.placed_at_0 Prysm.Checkpoint.Witness.EncodeFastPath.labels_fresh_at_0 0 (model_memmove 91 Prysm.Checkpoint.Witness.EncodeFastPath.placed_at_91 Prysm.Checkpoint.Witness.EncodeFastPath.labels_fresh_at_91 0)

end Prysm.Checkpoint.Witness.EncodeFunctionSpecAsNestedField
