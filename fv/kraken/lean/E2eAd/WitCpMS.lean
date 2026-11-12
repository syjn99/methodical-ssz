import E2eAd.CpSpecs
import Prysm.Checkpoint.WitnessEncodeFastPath

/-!
# `CpMAccC` holds on a concrete host

On the Checkpoint witness hosts of `Prysm.Checkpoint.WitnessDecodeAccept` (decoder, Epoch decoder, bump makeslice model,
memmove model) and `Prysm.Checkpoint.WitnessEncodeFastPath` (encoder, memmove model), the function specifications hold:
their hypotheses (`MakesliceC`, `MemmoveC`) are discharged by the runtime models. Together with the
witnesses `cp_accept_runs` / `cpm_runs_*` (which run the code on concrete states) this shows the
specifications are not vacuous. `*_spec_here` shows that the specification holds as an
instance on this host; it does not by itself show that the premises of a main theorem are satisfiable. That
(non-vacuity) comes from the run witnesses.
-/

open Machine Runtime TestTarget Machine.Witness Prysm.Checkpoint.Code E2eAd

namespace E2eAd.WitCpMS

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem cpm_spec_here : @CpMAccC Prysm.Checkpoint.Witness.EncodeFastPath.host 0 :=
  @cp_macc_holds Prysm.Checkpoint.Witness.EncodeFastPath.host 0 Prysm.Checkpoint.Witness.EncodeFastPath.hk0 Prysm.Checkpoint.Witness.EncodeFastPath.hf0 0 (rt_memmove 91 Prysm.Checkpoint.Witness.EncodeFastPath.hk91 Prysm.Checkpoint.Witness.EncodeFastPath.hf91 0)

end E2eAd.WitCpMS
