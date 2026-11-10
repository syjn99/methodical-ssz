# SPEC-BRIDGE: real Prysm `v1alpha1.Checkpoint` to EthLib (prysm-e2e E1.3)

Lean: `fv/kraken/lean/E2e/Spec.lean` (hand Desc and spec lemmas), `E2e/SpecChecker.lean` (generated from the Desc checker's input).

## 1. The hand Desc

`E2e.prysmCpDesc := .container ["epoch", "root"] [.uint 8, .byteVector 32]`, written from consensus-specs phase0:

```python
class Checkpoint(Container):
    epoch: Epoch   # Epoch = uint64
    root: Root     # Root = Bytes32
```

## 2. Evidence table to the Prysm Go type (`ab15ff70`, `proto/prysm/v1alpha1/attestation.pb.go:277`)

| Spec field | SSZ kind | Go field (order) | Go type and tag | Go layout (gc amd64, `prysm/ir/ir-mainnet.json` `go_fields`) | Machine code evidence (Go 1.26.10) |
| --- | --- | --- | --- | --- | --- |
| — | — | `state` (0) | `protoimpl.MessageState`, no SSZ | offset 0, size 8 | not read or written by the three functions |
| `epoch` | `uint64` | `Epoch` (1) | `primitives.Epoch` (`cast-type`, uint64) | offset 8, size 8 | decoder: `add $0x8,%rax` before the Epoch call; encoder: `mov 0x8(%rax),%r8` |
| `root` | `Bytes32` | `Root` (2) | `[]byte`, `ssz-size:"32"` | offset 16, size 24 (ptr, len, cap) | decoder writes 0x10/0x18/0x20; encoder `cmpq $0x20,0x18(%rax)` |
| — | — | `unknownFields` (3) | `protoimpl.UnknownFields` | offset 40, size 24 | not touched |
| — | — | `sizeCache` (4) | `protoimpl.SizeCache` (int32) | offset 64, size 4 | not touched |

Go struct size 72, alignment 8 (`go_size_gc_amd64`, `go_align_gc_amd64`).
Field order of the SSZ container = Go field order of the SSZ fields (Epoch, then Root), as in the generated code (`phase0.ssz.go:1962-1971`, `1984-1992`).

## 3. Lean facts

| Theorem | Content |
| --- | --- |
| `prysmCpDesc_checker` | the Desc checker's Desc `cpCheckerDesc` (generated from `prysm_v1alpha1.Checkpoint.desc.json`, sha256 `69170680…f644`, the record the checker accepted in `gen/desc/results/main.result.json`) has the same field list; only the names differ (Go names `Epoch`, `Root`) |
| `prysmCpDesc_eq_hand` | `prysmCpDesc = Fv1.cpDesc` (the reduced hand case): structurally equal, cited only |
| `pcp_spec_accepts_iff` | EthLib accepts `bs` iff `bs.size = 40` |
| `pcp_serialize` | `serialize prysmCpDesc g.toValue = .ok (uintBytes 8 g.epoch ++ g.root)` |
| `pcp_roundtrip` | `deserialize prysmCpDesc (pcpEnc g) = .ok g.toValue` |
| `pcp_accepted_is_enc` | an accepted input is `pcpEnc g` of the returned value |
| `pcp_spec_rejects` | `bs.size ≠ 40` → EthLib returns an error |

`PCp` (epoch : UInt64, root : Vector UInt8 32) is the SSZ content of a Go value in the EthLib domain (`len(Root) = 32`).
The other Go fields carry no SSZ value; the machine theorems keep their bytes as preserved resources.
The proofs of the spec lemmas are the text of `Fv1/SpecPrysm.lean` and `Fk/CpSpec.lean` with the names of this namespace.
They read EthLib only, no machine code.

## 4. Trust

`descterm.py` renders the JSON term as Lean text (trusted renderer, 3 kinds).
The producer and the checker are the phase1c tools; the checker's check for a Prysm type is consistency with the inventory, not a spec comparison (its own threat model).
That is why the theorems use the hand Desc, not the checker's.
