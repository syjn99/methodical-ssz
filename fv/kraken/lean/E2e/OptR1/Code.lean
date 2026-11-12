import Kraken.X64.Parser
import Machine.Include

/-!
# OPT-R1: code of the reserve encoder (Go 1.26.10 ELF `3ef7ac89…f602`)

`(*v1alpha1.Checkpoint).MarshalSSZTo` built from generator `ca191bb` with
`--reserve-marshal=Checkpoint`: one inserted statement at the top of the body,

    if cap(dst)-len(dst) < 40 { var z [40]byte; dst = append(dst, z[:]...)[:len(dst)] }

The `.S` is `fv/kraken/prysm/go1.26.10/opt-r1/link/norm` (`link/conv.py --norm`; `link/check.py`
(a)–(f) PASS in `../RESULT`). The other six functions of that directory are byte-identical to
`E2e.Code`'s; only this constant is new. Nothing about the baseline ELF `c6403c02…911e` changes.
The `.S` file is not a Lake input of the `E2e` library (no lakefile change): a changed file needs a
clean rebuild of the `E2e.OptR1` modules; its sha256 is pinned in `opt-r1/link/RESULT`.
-/

namespace E2e.OptR1.Code

/-- `(*v1alpha1.Checkpoint).MarshalSSZTo` with the 40-byte reserve (`phase0.ssz.go:1959`). -/
def CpMarshalO : Program := include_x64_rt "../prysm/go1.26.10/opt-r1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S"

end E2e.OptR1.Code
