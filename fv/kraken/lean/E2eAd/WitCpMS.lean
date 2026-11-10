import E2eAd.CpSpecs
import E2e.WitCpM

/-!
# `CpMAccC` holds on a concrete host (prysm-e2e A2)

On the Checkpoint witness hosts of `E2e.WitCpA` (decoder, Epoch decoder, bump makeslice model,
memmove model) and `E2e.WitCpM` (encoder, memmove model), the function specifications hold:
their hypotheses (`MakesliceC`, `MemmoveC`) are discharged by the runtime models. Together with the
witnesses `cp_accept_runs` / `cpm_runs_*` (which run the code on concrete states) this shows the
specifications are not vacuous. Audit AU-12 (A-06): `*_spec_here` shows that the specification holds as an
instance on this host; it does not by itself show that the premises of a main theorem are satisfiable. That
(non-vacuity) comes from the run witnesses.
-/

open Fk Fk.W E2e E2e.Code E2eAd

namespace E2eAd.WitCpMS

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem cpm_spec_here : @CpMAccC E2e.WitCpM.host 0 :=
  @cp_macc_holds E2e.WitCpM.host 0 E2e.WitCpM.hk0 E2e.WitCpM.hf0 0 (rt_memmove 91 E2e.WitCpM.hk91 E2e.WitCpM.hf91 0)

end E2eAd.WitCpMS
