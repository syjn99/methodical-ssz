# ENC2 survey: MarshalSSZTo of the 16 flat development types (Go 1.26.10 ELF `c6403c02…911e`)

Unit E2-P (preparation; no proof). Facts read from the committed `.S` files by `gen/e2e/enc2survey.py` (run from `fv/kraken`).
Checkpoint: `e2e/link`; BeaconBlockHeader: `e2e/bh/link`; Eth1Data: `e2e/e1/link`; the other 13: `e2e/enc2/link` (bundle in its `RESULT`).
Field name, Go offset, kind and size come from `prysm/ir/ir-mainnet.json` (v1alpha1); sizes are checked against the length-test immediates, the field count against the growslice count.
Register conventions at entry (Go ABIInternal): receiver `%rax`; dst ptr `%rbx`, len `%rcx`, cap `%rdi`.
"capacity test" = `cmp %newlen,%cap` before the field's growslice; `jae` jumps when cap >= newlen (unsigned); `jb` jumps to the growslice path.
"receiver reg" = base register of the block's load at the Go field offset (and its last reload from the frame before it).
No primitives `MarshalSSZTo` is called (overlay fields are in-line stores); see `e2e/enc2/callgraph.json`.

## Summary of distinct forms (mnemonic sequence of the field block, `nop` removed)

- uint64 store blocks: 22 fields, 9 distinct forms.
  - U0 (5: Checkpoint, PendingConsolidation, SyncAggregatorSelectionData, ValidatorBalance, VoluntaryExit): `lea mov lea movups movups mov cmp jae mov mov mov mov mov mov lea callq mov mov mov mov mov mov mov`
  - U1 (4: BeaconBlockHeader, BeaconBlockHeader, PendingPartialWithdrawal, SyncCommitteeMessage): `lea mov lea movups movups mov cmp jae mov mov mov mov mov lea callq mov mov mov mov mov mov mov`
  - U2 (3: Eth1Data, Deposit_Data, PendingDeposit): `mov add mov mov mov cmp jb mov jmp mov mov mov lea callq mov mov mov`
  - U3 (3: PendingPartialWithdrawal, PendingConsolidation, VoluntaryExit): `lea mov lea movups movups mov cmp jae mov mov mov mov mov lea callq mov mov mov mov mov mov`
  - U4 (2: BlobIdentifier, DepositMessage): `mov add mov mov mov cmp jb mov jmp mov mov mov lea callq mov mov`
  - U5 (2: SyncAggregatorSelectionData, ValidatorBalance): `add mov cmp jae mov mov mov mov mov lea callq mov mov mov mov mov`
  - U6 (1: PendingPartialWithdrawal): `add mov cmp jae mov mov mov mov mov lea callq mov mov mov mov mov mov`
  - U7 (1: SyncCommitteeMessage): `mov lea mov mov lea movups movups mov mov cmp jb mov jmp mov mov mov lea callq mov mov mov mov mov`
  - U8 (1: PendingDeposit): `mov lea mov mov lea movups movups mov mov cmp jb mov jmp mov mov mov lea callq mov mov mov mov`
- byte-append blocks: 24 fields, 5 distinct forms.
  - B0 (9: BeaconBlockHeader, BeaconBlockHeader, DepositMessage, Deposit_Data, PendingDeposit, PowBlock, PowBlock, HistoricalSummary, SigningData): `mov mov cmpq jne mov lea mov cmp jb mov jmp mov mov mov mov lea callq mov mov mov mov mov mov add mov callq`
  - B1 (8: Eth1Data, BlobIdentifier, DepositMessage, Deposit_Data, PendingDeposit, PowBlock, HistoricalSummary, SigningData): `mov cmpq jne mov lea cmp jae mov mov mov mov mov mov lea callq mov mov mov mov mov mov mov mov lea mov mov callq`
  - B2 (3: Checkpoint, BeaconBlockHeader, SyncCommitteeMessage): `mov cmpq jne lea cmp jae mov mov mov mov mov mov lea callq mov mov mov mov mov mov mov mov lea mov mov callq`
  - B3 (3: Eth1Data, Deposit_Data, PendingDeposit): `mov cmpq jne lea cmp jae mov mov mov mov lea callq mov mov mov mov mov mov add mov mov callq`
  - B4 (1: SyncCommitteeMessage): `mov cmpq jne lea cmp jae mov mov mov mov lea callq mov mov mov mov mov mov add mov callq`
- overlay (Slot, Epoch, ValidatorIndex, ... typed uint64): in-line (no call).

## Per type

### Checkpoint

File: `prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S` (91 lines).
Frame: `sub $0x68,%rsp` (line 7) = 104 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_123` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x68,%rsp` (7); morestack block label line 81, call line 86.
Spills after `sub`: `mov %rbx,0x80(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Epoch (Go +0x8, primitives.Epoch) | uint64 inline store via zeroed stack temp | 9–36 | none | `cmp %rdx,%rdi` (18); `jae L_7b` (19) -> line 34 (fast path jumps) | 28 `lea type__+387072(%rip),%rsi`; `nop` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (10)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | Root (Go +0x10, []byte) | byte append 32, memmove call | 37–63 | `cmpq $0x20,0x18(%rax)` (38); `jne L_108` (39) -> line 72 | `cmp %r9,%rdi` (41); `jae L_cf` (42) -> line 56 (fast path jumps) | 50 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (63) | rax (field load `mov 0x10(%rax),%r8` (37)) | r9 / rdi | `lea (%rbx,%rdx,1),%rax` (60); `mov $0x20,%ecx` (62) |

Epilogue (lines 64–71): `mov 0x60(%rsp),%rax`; `mov 0x50(%rsp),%rbx`; `mov 0x58(%rsp),%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x68,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 50]; `runtime.memmove` [63]; `runtime.morestack_noctxt.abi0` [86].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [63].
Length-reject targets (jne): line 72; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [11, 12, 13, 27].

### BeaconBlockHeader

File: `prysm/go1.26.10/e2e/bh/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo.S` (195 lines).
Frame: `sub $0x98,%rsp` (line 8) = 152 bytes; prologue large-frame guard: `lea -0x20(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_2ff` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `sub $0x98,%rsp` (8); morestack block label line 185, call line 190.
Spills after `sub`: `mov %rbx,0xb0(%rsp)` (9); `mov %rax,0xa8(%rsp)` (10).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Slot (Go +0x8, primitives.Slot) | uint64 inline store via zeroed stack temp | 11–36 | none | `cmp %rdx,%rdi` (20); `jae L_88` (21) -> line 34 (fast path jumps) | 28 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (12)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | ProposerIndex (Go +0x10, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 37–62 | none | `cmp %r8,%rdi` (46); `jae L_e9` (47) -> line 60 (fast path jumps) | 54 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r9,(%rbx,%rdx,1)` (62) | rax (field load `mov 0x10(%rax),%r9` (38)) | r8 / rdi | `mov %r9,(%rbx,%rdx,1)` (62) |
| 2 | ParentRoot (Go +0x18, []byte) | byte append 32, memmove call | 63–90 | `cmpq $0x20,0x20(%rax)` (64); `jne L_2e1` (66) -> line 176 | `cmp %r9,%rdi` (68); `jae L_14c` (69) -> line 83 (fast path jumps) | 77 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (90) | rax (field load `mov 0x18(%rax),%rdx` (63)) | r9 / rdi | `lea (%rbx,%r8,1),%rax` (87); `mov $0x20,%ecx` (89) |
| 3 | StateRoot (Go +0x30, []byte) | byte append 32, memmove call | 91–118 | `cmpq $0x20,0x38(%rdx)` (93); `jne L_2c2` (94) -> line 166 | `cmp %r9,%rcx` (98); `jb L_1a3` (99) -> line 102 (growslice path jumps) | 108 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (118) | rdx (field load `mov 0x30(%rdx),%rbx` (92)); reloaded by `mov 0xa8(%rsp),%rdx` (91) | r9 / rcx | `add %r8,%rax` (116); `mov $0x20,%ecx` (117) |
| 4 | BodyRoot (Go +0x48, []byte) | byte append 32, memmove call | 119–148 | `cmpq $0x20,0x50(%rdx)` (121); `jne L_2a4` (122) -> line 157 | `cmp %r8,%rcx` (127); `jb L_22f` (128) -> line 131 (growslice path jumps) | 137 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (148) | rdx (field load `mov 0x48(%rdx),%rbx` (120)); reloaded by `mov 0xa8(%rsp),%rdx` (119) | r8 / rcx | `add %rdx,%rax` (145); `mov $0x20,%ecx` (146) |

Epilogue (lines 149–156): `mov 0x90(%rsp),%rax`; `mov 0x38(%rsp),%rbx`; `mov 0x40(%rsp),%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x98,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 54, 77, 108, 137]; `runtime.memmove` [90, 118, 148]; `runtime.morestack_noctxt.abi0` [190].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [90, 118, 148].
Length-reject targets (jne): line 157, line 166, line 176; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [13, 14, 15, 39, 40, 41, 65, 126, 147, 174].

### Eth1Data

File: `prysm/go1.26.10/e2e/e1/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo.S` (119 lines).
Frame: `add $-0x80,%rsp` (line 8) = 128 bytes; prologue large-frame guard: `lea -0x8(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_1a1` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `add $-0x80,%rsp` (8); morestack block label line 109, call line 114.
Spills after `sub`: `mov %rbx,0x98(%rsp)` (9).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | DepositRoot (Go +0x8, []byte) | byte append 32, memmove call | 10–37 | `cmpq $0x20,0x10(%rax)` (11); `jne L_185` (12) -> line 99 | `cmp %r8,%rdi` (15); `jae L_7c` (16) -> line 30 (fast path jumps) | 24 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (37) | rax (field load `mov 0x8(%rax),%rdx` (10)) | r8 / rdi | `lea (%rcx,%rbx,1),%rax` (34); `mov $0x20,%ecx` (36) |
| 1 | DepositCount (Go +0x20, uint64) | uint64 inline store | 38–56 | none | `cmp %rbx,%rcx` (43); `jb L_c2` (44) -> line 47 (growslice path jumps) | 52 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %rsi,-0x8(%rbx,%rax,1)` (56) | rdx (field load `mov 0x20(%rdx),%rsi` (41)); reloaded by `mov 0x90(%rsp),%rdx` (40) | rbx / rcx | `mov %rsi,-0x8(%rbx,%rax,1)` (56) |
| 2 | BlockHash (Go +0x28, []byte) | byte append 32, memmove call | 57–81 | `cmpq $0x20,0x30(%rdx)` (58); `jne L_16a` (59) -> line 90 | `cmp %rdx,%rcx` (62); `jae L_132` (63) -> line 74 (fast path jumps) | 70 `lea type__+387072(%rip),%rsi`; `nop` | `callq runtime.memmove` (81) | rdx (field load `mov 0x28(%rdx),%r8` (57)) | rdx / rcx | `add %rbx,%rax` (78); `mov $0x20,%ecx` (80) |

Epilogue (lines 82–89): `mov 0x78(%rsp),%rax`; `mov 0x68(%rsp),%rbx`; `mov 0x60(%rsp),%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `sub $-0x80,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [24, 52, 70]; `runtime.memmove` [37, 81]; `runtime.morestack_noctxt.abi0` [114].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [37, 81].
Length-reject targets (jne): line 90, line 99; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [61, 69, 107].

### BlobIdentifier

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo.S` (79 lines).
Frame: `sub $0x68,%rsp` (line 7) = 104 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_101` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x68,%rsp` (7); morestack block label line 69, call line 74.
Spills after `sub`: `mov %rbx,0x80(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | BlockRoot (Go +0x8, []byte) | byte append 32, memmove call | 9–36 | `cmpq $0x20,0x10(%rax)` (10); `jne L_e6` (11) -> line 60 | `cmp %r8,%rdi` (14); `jae L_74` (15) -> line 29 (fast path jumps) | 23 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (36) | rax (field load `mov 0x8(%rax),%rdx` (9)) | r8 / rdi | `lea (%rbx,%rcx,1),%rax` (33); `mov $0x20,%ecx` (35) |
| 1 | Index (Go +0x20, uint64) | uint64 inline store | 37–54 | none | `cmp %rbx,%rcx` (42); `jb L_b7` (43) -> line 46 (growslice path jumps) | 51 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %rdx,-0x8(%rbx,%rax,1)` (54) | rdx (field load `mov 0x20(%rdx),%rdx` (40)); reloaded by `mov 0x78(%rsp),%rdx` (39) | rbx / rcx | `mov %rdx,-0x8(%rbx,%rax,1)` (54) |

Epilogue (lines 55–59): `xor %edi,%edi`; `xor %esi,%esi`; `add $0x68,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [23, 51]; `runtime.memmove` [36]; `runtime.morestack_noctxt.abi0` [74].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [36].
Length-reject targets (jne): line 60; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [].

### DepositMessage

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo.S` (117 lines).
Frame: `add $-0x80,%rsp` (line 8) = 128 bytes; prologue large-frame guard: `lea -0x8(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_19e` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `add $-0x80,%rsp` (8); morestack block label line 107, call line 112.
Spills after `sub`: `mov %rbx,0x98(%rsp)` (9).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | PublicKey (Go +0x0, []byte) | byte append 48, memmove call | 10–37 | `cmpq $0x30,0x8(%rax)` (11); `jne L_183` (12) -> line 98 | `cmp %r8,%rdi` (15); `jae L_7b` (16) -> line 30 (fast path jumps) | 24 `mov $0x30,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (37) | rax (field load `mov (%rax),%rdx` (10)) | r8 / rdi | `lea (%rcx,%rbx,1),%rax` (34); `mov $0x30,%ecx` (36) |
| 1 | WithdrawalCredentials (Go +0x18, []byte) | byte append 32, memmove call | 38–65 | `cmpq $0x20,0x20(%rdx)` (40); `jne L_168` (41) -> line 89 | `cmp %r9,%rcx` (45); `jb L_cc` (46) -> line 49 (growslice path jumps) | 55 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (65) | rdx (field load `mov 0x18(%rdx),%rbx` (39)); reloaded by `mov 0x90(%rsp),%rdx` (38) | r9 / rcx | `add %r8,%rax` (63); `mov $0x20,%ecx` (64) |
| 2 | Amount (Go +0x30, uint64) | uint64 inline store | 66–83 | none | `cmp %rbx,%rcx` (71); `jb L_139` (72) -> line 75 (growslice path jumps) | 80 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %rdx,-0x8(%rbx,%rax,1)` (83) | rdx (field load `mov 0x30(%rdx),%rdx` (69)); reloaded by `mov 0x90(%rsp),%rdx` (68) | rbx / rcx | `mov %rdx,-0x8(%rbx,%rax,1)` (83) |

Epilogue (lines 84–88): `xor %edi,%edi`; `xor %esi,%esi`; `sub $-0x80,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [24, 55, 80]; `runtime.memmove` [37, 65]; `runtime.morestack_noctxt.abi0` [112].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [37, 65].
Length-reject targets (jne): line 89, line 98; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [].

### Deposit_Data

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo.S` (156 lines).
Frame: `sub $0x88,%rsp` (line 8) = 136 bytes; prologue large-frame guard: `lea -0x10(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_261` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `sub $0x88,%rsp` (8); morestack block label line 146, call line 151.
Spills after `sub`: `mov %rbx,0xa0(%rsp)` (9).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | PublicKey (Go +0x8, []byte) | byte append 48, memmove call | 10–38 | `cmpq $0x30,0x10(%rax)` (11); `jne L_243` (12) -> line 137 | `cmp %r8,%rdi` (16); `jae L_88` (17) -> line 31 (fast path jumps) | 25 `mov $0x30,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (38) | rax (field load `mov 0x8(%rax),%rdx` (10)) | r8 / rdi | `lea (%rcx,%rbx,1),%rax` (35); `mov $0x30,%ecx` (37) |
| 1 | WithdrawalCredentials (Go +0x20, []byte) | byte append 32, memmove call | 39–68 | `cmpq $0x20,0x28(%rdx)` (41); `jne L_225` (43) -> line 128 | `cmp %r9,%rcx` (47); `jb L_e3` (48) -> line 51 (growslice path jumps) | 58 `lea type__+387072(%rip),%rsi`; `nop` | `callq runtime.memmove` (68) | rdx (field load `mov 0x20(%rdx),%rbx` (40)); reloaded by `mov 0x98(%rsp),%rdx` (39) | r9 / rcx | `add %r8,%rax` (66); `mov $0x20,%ecx` (67) |
| 2 | Amount (Go +0x38, uint64) | uint64 inline store | 69–87 | none | `cmp %rbx,%rcx` (74); `jb L_154` (75) -> line 78 (growslice path jumps) | 83 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %rsi,-0x8(%rbx,%rax,1)` (87) | rdx (field load `mov 0x38(%rdx),%rsi` (72)); reloaded by `mov 0x98(%rsp),%rdx` (71) | rbx / rcx | `mov %rsi,-0x8(%rbx,%rax,1)` (87) |
| 3 | Signature (Go +0x40, []byte) | byte append 96, memmove call | 88–110 | `cmpq $0x60,0x48(%rdx)` (89); `jne L_207` (90) -> line 119 | `cmp %rdx,%rcx` (92); `jae L_1c6` (93) -> line 103 (fast path jumps) | 99 `mov $0x60,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (110) | rdx (field load `mov 0x40(%rdx),%r8` (88)) | rdx / rcx | `add %rbx,%rax` (107); `mov $0x60,%ecx` (109) |

Epilogue (lines 111–118): `mov 0x80(%rsp),%rax`; `mov 0x68(%rsp),%rbx`; `mov 0x60(%rsp),%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x88,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [25, 58, 83, 99]; `runtime.memmove` [38, 68, 110]; `runtime.morestack_noctxt.abi0` [151].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [38, 68, 110].
Length-reject targets (jne): line 119, line 128, line 137; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [15, 42, 57].

### PendingPartialWithdrawal

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo.S` (99 lines).
Frame: `sub $0x90,%rsp` (line 8) = 144 bytes; prologue large-frame guard: `lea -0x18(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_147` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `sub $0x90,%rsp` (8); morestack block label line 88, call line 94.
Spills after `sub`: `mov %rbx,0xa8(%rsp)` (9); `mov %rax,0xa0(%rsp)` (10).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Index (Go +0x8, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 11–36 | none | `cmp %rdx,%rdi` (20); `jae L_88` (21) -> line 34 (fast path jumps) | 28 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (12)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | Amount (Go +0x10, uint64) | uint64 inline store | 37–54 | none | `cmp %rdx,%rdi` (39); `jae L_d3` (40) -> line 53 (fast path jumps) | 47 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,-0x8(%rdx,%rbx,1)` (54) | rax (field load `mov 0x10(%rax),%r8` (38)) | rdx / rdi | `mov %r8,-0x8(%rdx,%rbx,1)` (54) |
| 2 | WithdrawableEpoch (Go +0x18, primitives.Epoch) | uint64 inline store via zeroed stack temp | 55–79 | none | `cmp %r8,%rdi` (64); `jae L_128` (65) -> line 77 (fast path jumps) | 72 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r9,(%rbx,%rdx,1)` (79) | rax (field load `mov 0x18(%rax),%r9` (56)) | r8 / rdi | `mov %r9,(%rbx,%rdx,1)` (79) |

Epilogue (lines 80–87): `mov %rbx,%rax`; `mov %r8,%rbx`; `mov %rdi,%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x90,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 47, 72]; `runtime.morestack_noctxt.abi0` [94].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): none.
Length-reject targets (jne): none.
`nop` lines: [13, 14, 15, 57, 58, 59, 93].

### SyncCommitteeMessage

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo.S` (152 lines).
Frame: `sub $0xa8,%rsp` (line 8) = 168 bytes; prologue large-frame guard: `lea -0x30(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_243` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `sub $0xa8,%rsp` (8); morestack block label line 142, call line 147.
Spills after `sub`: `mov %rbx,0xc0(%rsp)` (9); `mov %rax,0xb8(%rsp)` (10).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Slot (Go +0x8, primitives.Slot) | uint64 inline store via zeroed stack temp | 11–36 | none | `cmp %rdx,%rdi` (20); `jae L_88` (21) -> line 34 (fast path jumps) | 28 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (12)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | BlockRoot (Go +0x10, []byte) | byte append 32, memmove call | 37–64 | `cmpq $0x20,0x18(%rax)` (38); `jne L_225` (40) -> line 133 | `cmp %r9,%rdi` (42); `jae L_ec` (43) -> line 57 (fast path jumps) | 51 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (64) | rax (field load `mov 0x10(%rax),%r8` (37)) | r9 / rdi | `lea (%rbx,%rdx,1),%rax` (61); `mov $0x20,%ecx` (63) |
| 2 | ValidatorIndex (Go +0x28, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 65–93 | none | `cmp %rdx,%rcx` (78); `jb L_14f` (79) -> line 82 (growslice path jumps) | 87 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rax,%rbx,1)` (93) | rsi (field load `mov 0x28(%rsi),%rdi` (68)); reloaded by `mov 0xb8(%rsp),%rsi` (67) | rdx / rcx | `mov %r8,(%rax,%rbx,1)` (93) |
| 3 | Signature (Go +0x30, []byte) | byte append 96, memmove call | 94–115 | `cmpq $0x60,0x38(%rsi)` (95); `jne L_207` (96) -> line 124 | `cmp %r8,%rcx` (98); `jae L_1c9` (99) -> line 109 (fast path jumps) | 105 `mov $0x60,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (115) | rsi (field load `mov 0x30(%rsi),%rbx` (94)) | r8 / rcx | `add %rdx,%rax` (113); `mov $0x60,%ecx` (114) |

Epilogue (lines 116–123): `mov 0xa0(%rsp),%rax`; `mov 0x48(%rsp),%rbx`; `mov 0x50(%rsp),%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0xa8,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 51, 87, 105]; `runtime.memmove` [64, 115]; `runtime.morestack_noctxt.abi0` [147].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [64, 115].
Length-reject targets (jne): line 124, line 133; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [13, 14, 15, 39, 69, 70, 71, 77].

### PendingConsolidation

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo.S` (79 lines).
Frame: `sub $0x70,%rsp` (line 7) = 112 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_f5` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x70,%rsp` (7); morestack block label line 69, call line 74.
Spills after `sub`: `mov %rbx,0x88(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | SourceIndex (Go +0x8, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 9–35 | none | `cmp %rdx,%rdi` (18); `jae L_80` (19) -> line 33 (fast path jumps) | 27 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rbx,%rcx,1)` (35) | rax (field load `mov 0x8(%rax),%r8` (10)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (35) |
| 1 | TargetIndex (Go +0x10, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 36–60 | none | `cmp %r8,%rdi` (45); `jae L_d9` (46) -> line 58 (fast path jumps) | 53 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r9,(%rbx,%rdx,1)` (60) | rax (field load `mov 0x10(%rax),%r9` (37)) | r8 / rdi | `mov %r9,(%rbx,%rdx,1)` (60) |

Epilogue (lines 61–68): `mov %rbx,%rax`; `mov %r8,%rbx`; `mov %rdi,%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x70,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [27, 53]; `runtime.morestack_noctxt.abi0` [74].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): none.
Length-reject targets (jne): none.
`nop` lines: [11, 12, 13, 38, 39, 40].

### PendingDeposit

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo.S` (182 lines).
Frame: `sub $0xc0,%rsp` (line 8) = 192 bytes; prologue large-frame guard: `lea -0x48(%rsp),%r12` (3); `cmp 0x10(%r14),%r12` (4); `jbe L_2e1` (5); then `push %rbp` (6); `mov %rsp,%rbp` (7); `sub $0xc0,%rsp` (8); morestack block label line 172, call line 177.
Spills after `sub`: `mov %rbx,0xd8(%rsp)` (9).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | PublicKey (Go +0x8, []byte) | byte append 48, memmove call | 10–38 | `cmpq $0x30,0x10(%rax)` (11); `jne L_2c2` (12) -> line 162 | `cmp %r8,%rdi` (16); `jae L_88` (17) -> line 31 (fast path jumps) | 25 `mov $0x30,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (38) | rax (field load `mov 0x8(%rax),%rdx` (10)) | r8 / rdi | `lea (%rbx,%rcx,1),%rax` (35); `mov $0x30,%ecx` (37) |
| 1 | WithdrawalCredentials (Go +0x20, []byte) | byte append 32, memmove call | 39–67 | `cmpq $0x20,0x28(%rdx)` (41); `jne L_2a4` (42) -> line 153 | `cmp %r9,%rcx` (47); `jb L_ef` (48) -> line 51 (growslice path jumps) | 57 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (67) | rdx (field load `mov 0x20(%rdx),%rbx` (40)); reloaded by `mov 0xd0(%rsp),%rdx` (39) | r9 / rcx | `add %r8,%rax` (65); `mov $0x20,%ecx` (66) |
| 2 | Amount (Go +0x38, uint64) | uint64 inline store | 68–87 | none | `cmp %rbx,%rcx` (74); `jb L_16f` (75) -> line 78 (growslice path jumps) | 83 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %rsi,-0x8(%rbx,%rax,1)` (87) | rdx (field load `mov 0x38(%rdx),%rsi` (71)); reloaded by `mov 0xd0(%rsp),%rdx` (70) | rbx / rcx | `mov %rsi,-0x8(%rbx,%rax,1)` (87) |
| 3 | Signature (Go +0x40, []byte) | byte append 96, memmove call | 88–110 | `cmpq $0x60,0x48(%rdx)` (89); `jne L_286` (90) -> line 144 | `cmp %r9,%rcx` (92); `jae L_1e8` (93) -> line 103 (fast path jumps) | 99 `mov $0x60,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (110) | rdx (field load `mov 0x40(%rdx),%r8` (88)) | r9 / rcx | `add %rbx,%rax` (107); `mov $0x60,%ecx` (109) |
| 4 | Slot (Go +0x58, primitives.Slot) | uint64 inline store via zeroed stack temp | 111–137 | none | `cmp %rdx,%rcx` (123); `jb L_249` (124) -> line 127 (growslice path jumps) | 132 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rax,%rbx,1)` (137) | rsi (field load `mov 0x58(%rsi),%rsi` (114)); reloaded by `mov 0xd0(%rsp),%rsi` (113) | rdx / rcx | `mov %r8,(%rax,%rbx,1)` (137) |

Epilogue (lines 138–143): `mov %rdx,%rbx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0xc0,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [25, 57, 83, 99, 132]; `runtime.memmove` [38, 67, 110]; `runtime.morestack_noctxt.abi0` [177].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [38, 67, 110].
Length-reject targets (jne): line 144, line 153, line 162; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [15, 46, 73, 115, 116, 117, 170].

### PowBlock

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo.S` (153 lines).
Frame: `sub $0x50,%rsp` (line 7) = 80 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_20d` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x50,%rsp` (7); morestack block label line 143, call line 148.
Spills after `sub`: `mov %rbx,0x68(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | BlockHash (Go +0x0, []byte) | byte append 32, memmove call | 9–37 | `cmpq $0x20,0x8(%rax)` (10); `jne L_1f2` (12) -> line 134 | `cmp %r8,%rdi` (15); `jae L_6b` (16) -> line 30 (fast path jumps) | 24 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (37) | rax (field load `mov (%rax),%rdx` (9)) | r8 / rdi | `lea (%rbx,%rcx,1),%rax` (34); `mov $0x20,%ecx` (36) |
| 1 | ParentHash (Go +0x18, []byte) | byte append 32, memmove call | 38–66 | `cmpq $0x20,0x20(%rdx)` (40); `jne L_1d7` (41) -> line 125 | `cmp %r9,%rcx` (45); `jb L_b9` (46) -> line 49 (growslice path jumps) | 55 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (66) | rdx (field load `mov 0x18(%rdx),%rbx` (39)); reloaded by `mov 0x60(%rsp),%rdx` (38) | r9 / rcx | `add %r8,%rax` (63); `mov $0x20,%ecx` (64) |
| 2 | TotalDifficulty (Go +0x30, []byte) | byte append 32, memmove call | 67–94 | `cmpq $0x20,0x38(%rdx)` (69); `jne L_1bc` (70) -> line 116 | `cmp %r8,%rcx` (74); `jb L_133` (75) -> line 78 (growslice path jumps) | 84 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (94) | rdx (field load `mov 0x30(%rdx),%rbx` (68)); reloaded by `mov 0x60(%rsp),%rdx` (67) | r8 / rcx | `add %rdx,%rax` (92); `mov $0x20,%ecx` (93) |

Epilogue (lines 95–115): `mov 0x48(%rsp),%rbx`; `mov %rbx,%rdx`; `sub %rsp,%rdx`; `lea 0x60(%rsp),%rsi`; `sub %rsp,%rsi`; `cmp %rsi,%rdx`; `jb L_1a3`; `mov 0x30(%rsp),%rbx`; `mov 0x38(%rsp),%rcx`; `mov 0x48(%rsp),%rax`; `jmp L_1b2`; `L_1a3:`; `mov $0x1,%eax`; `mov 0x30(%rsp),%rcx`; `callq runtime.moveSliceNoCapNoScan`; `L_1b2:`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x50,%rsp`; `pop %rbp`; `retq`.
Epilogue branch: `jb L_1a3` (line 101) -> line 106.
Runtime callees in the function (call lines): `runtime.growslice` [24, 55, 84]; `runtime.memmove` [37, 66, 94]; `runtime.morestack_noctxt.abi0` [148]; `runtime.moveSliceNoCapNoScan` [109].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [37, 66, 94]; `runtime.moveSliceNoCapNoScan` [109].
Length-reject targets (jne): line 116, line 125, line 134; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [11, 65].

### HistoricalSummary

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo.S` (115 lines).
Frame: `sub $0x50,%rsp` (line 7) = 80 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_17d` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x50,%rsp` (7); morestack block label line 105, call line 110.
Spills after `sub`: `mov %rbx,0x68(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | BlockSummaryRoot (Go +0x8, []byte) | byte append 32, memmove call | 9–36 | `cmpq $0x20,0x10(%rax)` (10); `jne L_162` (11) -> line 96 | `cmp %r8,%rdi` (14); `jae L_6b` (15) -> line 29 (fast path jumps) | 23 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (36) | rax (field load `mov 0x8(%rax),%rdx` (9)) | r8 / rdi | `lea (%rbx,%rcx,1),%rax` (33); `mov $0x20,%ecx` (35) |
| 1 | StateSummaryRoot (Go +0x20, []byte) | byte append 32, memmove call | 37–65 | `cmpq $0x20,0x28(%rdx)` (39); `jne L_147` (40) -> line 87 | `cmp %r8,%rcx` (44); `jb L_b9` (45) -> line 48 (growslice path jumps) | 54 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (65) | rdx (field load `mov 0x20(%rdx),%rbx` (38)); reloaded by `mov 0x60(%rsp),%rdx` (37) | r8 / rcx | `add %rdx,%rax` (62); `mov $0x20,%ecx` (63) |

Epilogue (lines 66–86): `mov 0x48(%rsp),%rbx`; `mov %rbx,%rdx`; `sub %rsp,%rdx`; `lea 0x60(%rsp),%rsi`; `sub %rsp,%rsi`; `cmp %rsi,%rdx`; `jb L_12e`; `mov 0x30(%rsp),%rbx`; `mov 0x38(%rsp),%rcx`; `mov 0x48(%rsp),%rax`; `jmp L_13d`; `L_12e:`; `mov $0x1,%eax`; `mov 0x30(%rsp),%rcx`; `callq runtime.moveSliceNoCapNoScan`; `L_13d:`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x50,%rsp`; `pop %rbp`; `retq`.
Epilogue branch: `jb L_12e` (line 72) -> line 77.
Runtime callees in the function (call lines): `runtime.growslice` [23, 54]; `runtime.memmove` [36, 65]; `runtime.morestack_noctxt.abi0` [110]; `runtime.moveSliceNoCapNoScan` [80].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [36, 65]; `runtime.moveSliceNoCapNoScan` [80].
Length-reject targets (jne): line 87, line 96; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [64].

### SigningData

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo.S` (116 lines).
Frame: `sub $0x50,%rsp` (line 7) = 80 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_17d` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x50,%rsp` (7); morestack block label line 106, call line 111.
Spills after `sub`: `mov %rbx,0x68(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | ObjectRoot (Go +0x0, []byte) | byte append 32, memmove call | 9–37 | `cmpq $0x20,0x8(%rax)` (10); `jne L_162` (12) -> line 97 | `cmp %r8,%rdi` (15); `jae L_6b` (16) -> line 30 (fast path jumps) | 24 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (37) | rax (field load `mov (%rax),%rdx` (9)) | r8 / rdi | `lea (%rbx,%rcx,1),%rax` (34); `mov $0x20,%ecx` (36) |
| 1 | Domain (Go +0x18, []byte) | byte append 32, memmove call | 38–66 | `cmpq $0x20,0x20(%rdx)` (40); `jne L_147` (41) -> line 88 | `cmp %r8,%rcx` (45); `jb L_b9` (46) -> line 49 (growslice path jumps) | 55 `mov $0x20,%edi`; `lea type__+387072(%rip),%rsi` | `callq runtime.memmove` (66) | rdx (field load `mov 0x18(%rdx),%rbx` (39)); reloaded by `mov 0x60(%rsp),%rdx` (38) | r8 / rcx | `add %rdx,%rax` (63); `mov $0x20,%ecx` (64) |

Epilogue (lines 67–87): `mov 0x48(%rsp),%rbx`; `mov %rbx,%rdx`; `sub %rsp,%rdx`; `lea 0x60(%rsp),%rsi`; `sub %rsp,%rsi`; `cmp %rsi,%rdx`; `jb L_12e`; `mov 0x30(%rsp),%rbx`; `mov 0x38(%rsp),%rcx`; `mov 0x48(%rsp),%rax`; `jmp L_13d`; `L_12e:`; `mov $0x1,%eax`; `mov 0x30(%rsp),%rcx`; `callq runtime.moveSliceNoCapNoScan`; `L_13d:`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x50,%rsp`; `pop %rbp`; `retq`.
Epilogue branch: `jb L_12e` (line 73) -> line 78.
Runtime callees in the function (call lines): `runtime.growslice` [24, 55]; `runtime.memmove` [37, 66]; `runtime.morestack_noctxt.abi0` [111]; `runtime.moveSliceNoCapNoScan` [81].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): `runtime.memmove` [37, 66]; `runtime.moveSliceNoCapNoScan` [81].
Length-reject targets (jne): line 88, line 97; each block: `mov ssz.ErrBytesLength(%rip),%rdi` ... `retq`.
`nop` lines: [11, 65].

### SyncAggregatorSelectionData

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo.S` (72 lines).
Frame: `sub $0x68,%rsp` (line 7) = 104 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_d6` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x68,%rsp` (7); morestack block label line 62, call line 67.
Spills after `sub`: `mov %rbx,0x80(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Slot (Go +0x8, primitives.Slot) | uint64 inline store via zeroed stack temp | 9–36 | none | `cmp %rdx,%rdi` (18); `jae L_7b` (19) -> line 34 (fast path jumps) | 28 `lea type__+387072(%rip),%rsi`; `nop` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (10)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | SubcommitteeIndex (Go +0x10, uint64) | uint64 inline store | 37–53 | none | `cmp %rdx,%rdi` (39); `jae L_be` (40) -> line 52 (fast path jumps) | 47 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,-0x8(%rdx,%rbx,1)` (53) | rax (field load `mov 0x10(%rax),%r8` (38)) | rdx / rdi | `mov %r8,-0x8(%rdx,%rbx,1)` (53) |

Epilogue (lines 54–61): `mov %rbx,%rax`; `mov %rdx,%rbx`; `mov %rdi,%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x68,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 47]; `runtime.morestack_noctxt.abi0` [67].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): none.
Length-reject targets (jne): none.
`nop` lines: [11, 12, 13, 27].

### ValidatorBalance

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo.S` (72 lines).
Frame: `sub $0x68,%rsp` (line 7) = 104 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_d6` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x68,%rsp` (7); morestack block label line 62, call line 67.
Spills after `sub`: `mov %rbx,0x80(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Index (Go +0x8, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 9–36 | none | `cmp %rdx,%rdi` (18); `jae L_7b` (19) -> line 34 (fast path jumps) | 28 `lea type__+387072(%rip),%rsi`; `nop` | `mov %r8,(%rbx,%rcx,1)` (36) | rax (field load `mov 0x8(%rax),%r8` (10)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (36) |
| 1 | Balance (Go +0x10, uint64) | uint64 inline store | 37–53 | none | `cmp %rdx,%rdi` (39); `jae L_be` (40) -> line 52 (fast path jumps) | 47 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,-0x8(%rdx,%rbx,1)` (53) | rax (field load `mov 0x10(%rax),%r8` (38)) | rdx / rdi | `mov %r8,-0x8(%rdx,%rbx,1)` (53) |

Epilogue (lines 54–61): `mov %rbx,%rax`; `mov %rdx,%rbx`; `mov %rdi,%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x68,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [28, 47]; `runtime.morestack_noctxt.abi0` [67].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): none.
Length-reject targets (jne): none.
`nop` lines: [11, 12, 13, 27].

### VoluntaryExit

File: `prysm/go1.26.10/e2e/enc2/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo.S` (79 lines).
Frame: `sub $0x70,%rsp` (line 7) = 112 bytes; prologue small guard: `cmp 0x10(%r14),%rsp` (3); `jbe L_f5` (4); then `push %rbp` (5); `mov %rsp,%rbp` (6); `sub $0x70,%rsp` (7); morestack block label line 69, call line 74.
Spills after `sub`: `mov %rbx,0x88(%rsp)` (8).

| # | field | kind | block lines | length test (line, branch) | capacity test (line, branch) | growslice (line) | commit (line) | receiver reg | len / cap regs at test | dst addr |
| - | - | - | - | - | - | - | - | - | - | - |
| 0 | Epoch (Go +0x8, primitives.Epoch) | uint64 inline store via zeroed stack temp | 9–35 | none | `cmp %rdx,%rdi` (18); `jae L_80` (19) -> line 33 (fast path jumps) | 27 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r8,(%rbx,%rcx,1)` (35) | rax (field load `mov 0x8(%rax),%r8` (10)) | rdx / rdi | `mov %r8,(%rbx,%rcx,1)` (35) |
| 1 | ValidatorIndex (Go +0x10, primitives.ValidatorIndex) | uint64 inline store via zeroed stack temp | 36–60 | none | `cmp %r8,%rdi` (45); `jae L_d9` (46) -> line 58 (fast path jumps) | 53 `mov $0x8,%edi`; `lea type__+387072(%rip),%rsi` | `mov %r9,(%rbx,%rdx,1)` (60) | rax (field load `mov 0x10(%rax),%r9` (37)) | r8 / rdi | `mov %r9,(%rbx,%rdx,1)` (60) |

Epilogue (lines 61–68): `mov %rbx,%rax`; `mov %r8,%rbx`; `mov %rdi,%rcx`; `xor %edi,%edi`; `xor %esi,%esi`; `add $0x70,%rsp`; `pop %rbp`; `retq`.
Runtime callees in the function (call lines): `runtime.growslice` [27, 53]; `runtime.morestack_noctxt.abi0` [74].
Calls in-line between `sub` and the first `retq` (growslice sites excluded; the fast path passes these lines unless a branch above jumps over them): none.
Length-reject targets (jne): none.
`nop` lines: [11, 12, 13, 38, 39, 40].
