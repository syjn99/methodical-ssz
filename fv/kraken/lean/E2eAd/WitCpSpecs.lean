import E2eAd.CpSpecs
import E2e.WitCpA

/-!
# `CpUAccC` and `CpMAccC` hold on a concrete host

On the Checkpoint witness hosts of `E2e.WitCpA` (decoder, Epoch decoder, bump makeslice model,
memmove model); the encoder instance is `E2eAd/WitCpMS.lean` (one witness host per file), the function specifications hold:
their hypotheses (`MakesliceC`, `MemmoveC`) are discharged by the runtime models. Together with the
witnesses `cp_accept_runs` / `cpm_runs_*` (which run the code on concrete states) this shows the
specifications are not vacuous. `*_spec_here` shows that the specification holds as an
instance on this host; it does not by itself show that the premises of a main theorem are satisfiable. That
(non-vacuity) comes from the run witnesses.
-/

open Machine Runtime TestTarget Machine.Witness E2e E2e.Code E2eAd

namespace E2eAd.WitCpSpecs

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem cpu_spec_here : @CpUAccC E2e.WitCpA.host bumpHeap 8 :=
  @cp_uacc_holds E2e.WitCpA.host 9 E2e.WitCpA.hk9 E2e.WitCpA.hf9 117 E2e.WitCpA.hk117 E2e.WitCpA.hf117 bumpHeap 8
    (bump_makeslice1 180 E2e.WitCpA.hk180 E2e.WitCpA.hf180 _) (rt_memmove 186 E2e.WitCpA.hk186 E2e.WitCpA.hf186 8)

end E2eAd.WitCpSpecs
