import Kraken.X64.Parser
import Machine.Include
import Prysm.SyncCommittee.Code

/-!
# Code of the SyncAggregate and SyncCommittee function set (Go 1.26.10 ELF `c6403c02…911e`)

Each constant includes a `.S` file of `fv/kraken/prysm/go1.26.10/e2e/lv/link/norm`
(`link/conv.py --norm` of the same ELF as `Prysm.Checkpoint.Code`, `Prysm.AttestationData.Code` and `Prysm.Deposit_Data.Code`;
written by `gen/e2e/lvlink.py filter` and `conv.py`; `link/check.py` (a)–(f) PASS in `prysm/go1.26.10/e2e/lv/link/RESULT`).
The directory is a Lake `input_dir` of the `Prysm` library (`lakefile.toml`), so Lake rebuilds
these modules when a `.S` file changes. `IndexedAttestation` is not in the committed set
(link check (d) failed on this host's clang: Apple clang 21 rejects the GNU objdump spelling
`0xffffff1c(%rdi)` of the displacement -228).
After the split of this module, the declarations of the other types are in `Prysm/SyncCommittee/Code.lean`.
-/

namespace Prysm.SyncAggregate.Code

/-- `(*v1alpha1.SyncAggregate).UnmarshalSSZ` (protoc type, `altair.ssz.go`). -/
def unmarshalSSZ : Program := include_x64_rt "../prysm/go1.26.10/e2e/lv/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ.S"
end Prysm.SyncAggregate.Code
