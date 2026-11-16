import Kraken.X64.Parser
import Machine.Include

/-!
# Code of the IndexedAttestation decoder (the Go 1.26.10 ELF of `prysm/go1.26.10/build-ids.txt`)

`unmarshalSSZ` includes the `.S` file of `fv/kraken/prysm/go1.26.10/link-set/norm`
(`link/convert_objdump.py --norm`, which writes a negative 32-bit displacement in signed form; `gen/checks/lists_and_vectors_link.py filter/data --with-indexed-attestation`;
`link/check.py` (a)–(f) PASS in `prysm/go1.26.10/link-set/RESULT`).
The directory is a Lake `input_dir` of the `Prysm` library (`lakefile.toml`).
-/

namespace Prysm.IndexedAttestation.Code

/-- `(*v1alpha1.IndexedAttestation).UnmarshalSSZ` (protoc type, `phase0.ssz.go:2819`). -/
def unmarshalSSZ : Program := include_x64_code "../prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ.S"

end Prysm.IndexedAttestation.Code
