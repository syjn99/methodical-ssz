# CALLGRAPH: Checkpoint / Epoch SSZ functions in the Go 1.26.10 ELF (Prysm end-to-end proof work, Checkpoint call graph step E1.1)

Generated from `callgraph.json` (`gen/e2e/callgraph.py` over the objdump of ELF `c6403c02…911e` and the gated `-gcflags=-m=2` log; job logs 02). Every number below is read from that JSON.

## 1. Functions and call sites

| Function | Scope | Address | Instructions | Calls |
| --- | --- | --- | --- | --- |
| `v1alpha1.(*Checkpoint).SizeSSZ` | in | `0xa1db00` | 2 | 0 |
| `v1alpha1.(*Checkpoint).MarshalSSZTo` | in | `0xa1db80` | 85 | 4 |
| `v1alpha1.(*Checkpoint).UnmarshalSSZ` | in | `0xa1dce0` | 98 | 8 |
| `primitives.(*Epoch).UnmarshalSSZ` | in (callee, function spec of the Epoch decoder step E2) | `0x69ece0` | 58 | 4 |
| `primitives.(*Epoch).MarshalSSZTo` | record only (inlined into Checkpoint.MarshalSSZTo; out-of-line body unused by it) | `0x69ede0` | 47 | 2 |
| `primitives.(*Epoch).MarshalSSZ` | record only (inlined) | `0x69eea0` | 25 | 2 |
| `primitives.(*Epoch).SizeSSZ` | record only (inlined) | `0x69ef00` | 2 | 0 |

## 2. Call targets and their class (CONTRACTS.md: a = proved, b = contract, c = excluded by a premise)

| Caller | Site | Target | Class | How |
| --- | --- | --- | --- | --- |
| `(*Checkpoint).MarshalSSZTo` | `0xa1dbe0` | `runtime.growslice` | b | GrowsliceC (esz 1) |
| `(*Checkpoint).MarshalSSZTo` | `0xa1dc37` | `runtime.growslice` | b | GrowsliceC (esz 1) |
| `(*Checkpoint).MarshalSSZTo` | `0xa1dc6a` | `runtime.memmove` | b | MemmoveC |
| `(*Checkpoint).MarshalSSZTo` | `0xa1dcb7` | `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1dd20` | `primitives.(*Epoch).UnmarshalSSZ` | a | function spec EpUAccC, proved from machine code (ep_uacc_holds) |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1dd59` | `fmt.errorf` | b | FmtErrorfWC ('Epoch: %w', Checkpoint) / FmtErrorfDDC ('expected buffer of length %d received %d', Epoch) |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1dd6d` | `runtime.newobject` | c | nil-result branch after fmt.errorf: excluded by the contract's rax != 0 |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1ddac` | `runtime.makeslice` | b | MakesliceC (esz 1, uint8 type word) |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1ddd3` | `runtime.gcWriteBarrier2` | c | writeBarrier = 0 premise: the cmpl/je is proved to skip the call |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1ddf6` | `runtime.memmove` | b | MemmoveC |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1de26` | `runtime.gcWriteBarrier2` | c | writeBarrier = 0 premise: the cmpl/je is proved to skip the call |
| `(*Checkpoint).UnmarshalSSZ` | `0xa1de73` | `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |
| `(*Epoch).UnmarshalSSZ` | `0x69ed33` | `runtime.convT64` | b | ConvT64C |
| `(*Epoch).UnmarshalSSZ` | `0x69ed62` | `fmt.errorf` | b | FmtErrorfWC ('Epoch: %w', Checkpoint) / FmtErrorfDDC ('expected buffer of length %d received %d', Epoch) |
| `(*Epoch).UnmarshalSSZ` | `0x69ed74` | `runtime.newobject` | c | nil-result branch after fmt.errorf: excluded by the contract's rax != 0 |
| `(*Epoch).UnmarshalSSZ` | `0x69edc0` | `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |
| `(*Epoch).MarshalSSZTo` | `0x69ee2e` | `runtime.growslice` | b | GrowsliceC (esz 1) |
| `(*Epoch).MarshalSSZTo` | `0x69ee71` | `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |
| `(*Epoch).MarshalSSZ` | `0x69eece` | `runtime.growslice` | b | GrowsliceC (esz 1) |
| `(*Epoch).MarshalSSZ` | `0x69eeef` | `runtime.morestack_noctxt.abi0` | c | stack-guard premise g.stackguard0 < rsp: the jbe is proved not taken |

Unclassified call sites: 0.

## 3. Method mapping (inlining)

- machine code: Checkpoint.MarshalSSZTo calls Epoch.MarshalSSZTo/MarshalSSZ/SizeSSZ: **False**
- machine code: Checkpoint.UnmarshalSSZ calls Epoch.UnmarshalSSZ: **True**
- `-m=2` `can_inline_Epoch_MarshalSSZTo`: 1 line(s): `epoch.go:135:6: can inline (*Epoch).MarshalSSZTo with cost 39 as: method(*Epoch) func([]byte) ([]byte, error) { marshalled, err := ([]byte)(.autotmp_6), .autotm`
- `-m=2` `can_inline_Epoch_MarshalSSZ`: 1 line(s): `epoch.go:144:6: can inline (*Epoch).MarshalSSZ with cost 18 as: method(*Epoch) func() ([]byte, error) { marshalled := MarshalUint64([]byte{}, uint64(*e)); retur`
- `-m=2` `can_inline_Epoch_SizeSSZ`: 1 line(s): `epoch.go:150:6: can inline (*Epoch).SizeSSZ with cost 2 as: method(*Epoch) func() int { return 8 }`
- `-m=2` `can_inline_Epoch_UnmarshalSSZ`: 0 line(s)
- `-m=2` `cannot_inline_Epoch_UnmarshalSSZ`: 1 line(s): `epoch.go:126:6: cannot inline (*Epoch).UnmarshalSSZ: function too complex: cost 113 exceeds budget 80`
- `-m=2` `cp_marshal_inlines_Epoch_MarshalSSZTo`: 1 line(s): `phase0.ssz.go:1963:36: inlining call to primitives.(*Epoch).MarshalSSZTo`
- `-m=2` `cp_marshal_inlines_Epoch_MarshalSSZ`: 1 line(s): `phase0.ssz.go:1963:36: inlining call to primitives.(*Epoch).MarshalSSZ`
- `-m=2` `cp_unmarshal_inlines_Epoch_UnmarshalSSZ`: 0 line(s)
- `-m=2` `cp_unmarshal_inlines_Epoch_SizeSSZ`: 0 line(s)

Result: `(*Epoch).MarshalSSZTo`, `(*Epoch).MarshalSSZ` (and inside it `primitives.MarshalUint64`, `binary.littleEndian.AppendUint64`) are inlined into `(*Checkpoint).MarshalSSZTo` (phase0.ssz.go:1963).
The inlined body is proved as part of the caller (Checkpoint encoder step E4): the 32-byte zeroed stack temp at `0x30(%rsp)` holds the 8 epoch bytes, then the append copies them to `dst[len:len+8]`.
The inlined `Epoch.MarshalSSZTo` cannot fail (`err` is always nil), so the compiler removed the `fmt.Errorf("Epoch: %w")` branch of the encoder: there is no machine-code error site for it (no `fmt.errorf` call in `Checkpoint.MarshalSSZTo`).
`(*Epoch).UnmarshalSSZ` is not inlined (cost 113 > 80) and is called out of line from `(*Checkpoint).UnmarshalSSZ`: it is proved as a function spec (Epoch decoder step E2, `EpUAccC`/`ep_uacc_holds`).
`(*Epoch).SizeSSZ` is inlined into `(*Epoch).UnmarshalSSZ` (constant 8 in `cmp $0x8,%rcx`).
The out-of-line bodies of `Epoch.MarshalSSZTo/MarshalSSZ/SizeSSZ` exist in the ELF and are in the link tables for the record; no theorem uses them.

## 4. Out of scope

`(*Checkpoint).MarshalSSZ` (allocates and calls MarshalSSZTo), `(*Checkpoint).HashTreeRoot`, `HashTreeRootWith` exist in the source (phase0.ssz.go:1954, 1997) but are not in this function set: the obligations of this run are SizeSSZ, MarshalSSZTo, UnmarshalSSZ (`gen/frozen/THEOREMS.json`).

