# Call graph and method mapping: real `v1alpha1.AttestationData` (Prysm end-to-end proof work, AttestationData set-up step A1, Go 1.26.10 ELF `c6403c02…911e`)

Generated from `callgraph.json` (`gen/e2e/adlink.py callgraph <objdump> callgraph.json <m2.log>`; the m2 log is the gated `go build -gcflags=…=-m=2` output of job 02, the same run as `../gcflags-m2.txt`).

| Function | Instructions | Scope | Calls (count) |
| --- | --- | --- | --- |
| `v1alpha1.(*AttestationData).SizeSSZ` | 2 | in (encoder step A4, size) | none |
| `v1alpha1.(*AttestationData).MarshalSSZTo` | 218 | in (encoder step A4) | `runtime.growslice` ×3, `runtime.memmove` ×1, `runtime.newobject` ×4, `runtime.gcWriteBarrier2` ×2, `v1alpha1.(*Checkpoint).MarshalSSZTo` ×2, `fmt.errorf` ×2, `runtime.morestack_noctxt.abi0` ×1 |
| `v1alpha1.(*AttestationData).UnmarshalSSZ` | 220 | in (decoder step A3) | `primitives.(*Slot).UnmarshalSSZ` ×1, `fmt.errorf` ×4, `runtime.newobject` ×6, `primitives.(*CommitteeIndex).UnmarshalSSZ` ×1, `runtime.makeslice` ×1, `runtime.gcWriteBarrier2` ×4, `runtime.memmove` ×1, `v1alpha1.(*Checkpoint).UnmarshalSSZ` ×2, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*Slot).UnmarshalSSZ` | 58 | in (callee, function spec SlUAccC, callee step A2) | `runtime.convT64` ×1, `fmt.errorf` ×1, `runtime.newobject` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*Slot).MarshalSSZTo` | 47 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | `runtime.growslice` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*Slot).MarshalSSZ` | 25 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | `runtime.growslice` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*Slot).SizeSSZ` | 2 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | none |
| `primitives.(*CommitteeIndex).UnmarshalSSZ` | 58 | in (callee, function spec CiUAccC, callee step A2) | `runtime.convT64` ×1, `fmt.errorf` ×1, `runtime.newobject` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*CommitteeIndex).MarshalSSZTo` | 47 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | `runtime.growslice` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*CommitteeIndex).MarshalSSZ` | 25 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | `runtime.growslice` ×1, `runtime.morestack_noctxt.abi0` ×1 |
| `primitives.(*CommitteeIndex).SizeSSZ` | 2 | record only (inlined into AttestationData.MarshalSSZTo or unused; out-of-line body unused) | none |

Contract class of each call target (CONTRACTS.md classes: a = proved function spec, b = runtime contract, c = excluded by a premise):

| Target | Class | How |
| --- | --- | --- |
| `fmt.errorf` | b | FmtErrorfWC (field wraps 'Slot: %w', 'CommitteeIndex: %w', 'Source: %w', 'Target: %w'); decoder: unreachable_mc under the callee specs; encoder Source/Target: reachable when a child Root has len != 32 |
| `primitives.(*CommitteeIndex).UnmarshalSSZ` | a | function spec CiUAccC, proved from machine code |
| `primitives.(*Slot).UnmarshalSSZ` | a | function spec SlUAccC, proved from machine code |
| `v1alpha1.(*Checkpoint).MarshalSSZTo` | a | function spec CpMAccC = cp_e2e_marshal_main (its runtime contracts stay hypotheses) |
| `v1alpha1.(*Checkpoint).UnmarshalSSZ` | a | function spec CpUAccC = cp_e2e_accept_main (its runtime contracts stay hypotheses) |
| `runtime.convT64` | b | ConvT64C (Slot/CommitteeIndex length reject only; not on the accept specs) |
| `runtime.gcWriteBarrier2` | c | writeBarrier = 0 premise: the cmpl/jne is proved to skip the call |
| `runtime.growslice` | b | GrowsliceC (esz 1); main theorem: capacity sufficient, not called |
| `runtime.makeslice` | b | MakesliceC (esz 1, uint8 type word, cnt 32) |
| `runtime.memmove` | b | MemmoveC (n = 32) |
| `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |
| `runtime.newobject` | b | NewobjectC (Checkpoint type word, 72 bytes): decoder Source/Target, encoder nil Source/Target; after fmt.errorf: the nil-result branch, excluded by rax != 0 |

Inlining (`-m=2` lines, program count):

- `cannot_inline_Slot_UnmarshalSSZ`: 1 — `slot.go:183:6: cannot inline (*Slot).UnmarshalSSZ: function too complex: cost 113 exceeds budget 80`
- `can_inline_Slot_MarshalSSZTo`: 1 — `slot.go:192:6: can inline (*Slot).MarshalSSZTo with cost 39 as: method(*Slot) func([]byte) ([]byte, error) { marshalled, err := ([]byte)(.au`
- `cannot_inline_CommitteeIndex_UnmarshalSSZ`: 1 — `committee_index.go:28:6: cannot inline (*CommitteeIndex).UnmarshalSSZ: function too complex: cost 113 exceeds budget 80`
- `can_inline_CommitteeIndex_MarshalSSZTo`: 1 — `committee_index.go:37:6: can inline (*CommitteeIndex).MarshalSSZTo with cost 39 as: method(*CommitteeIndex) func([]byte) ([]byte, error) { m`
- `ad_marshal_inlines_Slot_MarshalSSZTo`: 1 — `phase0.ssz.go:239:35: inlining call to primitives.(*Slot).MarshalSSZTo`
- `ad_marshal_inlines_CommitteeIndex_MarshalSSZTo`: 1 — `phase0.ssz.go:244:45: inlining call to primitives.(*CommitteeIndex).MarshalSSZTo`
- `ad_unmarshal_inlines_any_primitives`: 0

Machine code: AttestationData.MarshalSSZTo calls no Slot/CommitteeIndex method: True (the two 8-byte appends are inline: growslice sites 1 and 2). The decoder calls `(*Slot).UnmarshalSSZ` and `(*CommitteeIndex).UnmarshalSSZ` out of line (`cannot inline … cost 113`).

Code facts used by the decoder step A3 and the encoder step A4 (from the `.S`):

- Decoder: frame `sub $0x70`; `cmp $0x80,%rcx; jne → ssz.ErrSize`; Slot at receiver +8, CommitteeIndex +16 (callee calls, len 8); `makeslice(uint8, 0, 32)` → `BeaconBlockRoot` header (+24/+32/+40) with `writeBarrier` checks, `memmove(32)`; `Source = new(Checkpoint)` and `Target = new(Checkpoint)` **unconditionally** (`newobject(type__+1289312)`, 72 bytes; no nil test in the decoder), each followed by `(*Checkpoint).UnmarshalSSZ(buf[48:88])` / `(buf[88:128])` (len 40); four `fmt.errorf` field wraps on callee errors.
- Encoder: frame `sub $0xb0`; Slot and CommitteeIndex appends inline (growslice sites 1, 2); `cmpq $0x20,0x20(%rax); jne → ssz.ErrBytesLength`; BeaconBlockRoot append (growslice site 3, memmove 32); `if Source == nil { Source = new(Checkpoint) }` (newobject + store with writeBarrier check), call `(*Checkpoint).MarshalSSZTo`; on its error `fmt.errorf("Source: %w")` (reachable: a Source Root of length ≠ 32); the same for Target.
- SizeSSZ: `mov $0x80,%eax; retq`.
- The ELF's Checkpoint `abi.Type` (the `newobject` argument, data item `adCpType`) has `Size_ = 0x48 = 72`, the IR size of `E2e.cpGoSize`.

Out of scope: `AttestationData.MarshalSSZ`, `HashTreeRoot*`, the out-of-line `Slot`/`CommitteeIndex` `MarshalSSZTo`/`MarshalSSZ`/`SizeSSZ` bodies (record only).
