# `--gen4` survey: padding, receiver registers and call set-ups in the 10 development decoders

Evidence for the `--gen4` lemma unit (survey made before the design note; development data only).
Source: the normalised `.S` files of `UnmarshalSSZ` under `prysm/go1.26.10/e2e/{link,ad,bh,e1,h3,h4,h5}/link/norm` and `prysm/go1.26.10/e2e/link/norm` (ELF `c6403c02…911e`).
Directive index = `.S` line − 1. `F` stands for the function's own label prefix, `prim.` for `consensus_types_primitives`, `v1.` for `proto_prysm_v1alpha1`.
The table was written by a scratch script (regular expressions on the `.S` text); the script is not committed. A set-up is the run of directives after the previous label, jump, call or `cmp` up to the `callq`.

## Summary

| Fact | Count |
| --- | --- |
| decoders (container / hold-out types) | 10 |
| `nop` directives (all the one-byte form) | 46 |
| `nop` on an accept path | head, index 8: 10 (every type); before a callee `callq`: 2 (Checkpoint 16, BeaconBlockHeader 54); after a callee `callq`: 1 (PendingConsolidation 56); before `callq runtime.makeslice`: 2 (Deposit_Data 50, SyncCommitteeMessage 123); between `mov dS(%rsp),%rT` and `jmp` in a byte tail: 2 (Checkpoint 76, BeaconBlockHeader 114) |
| callee `UnmarshalSSZ` calls | 13 (11 `uint64`-overlay, 2 `*Checkpoint`) |
| `runtime.makeslice` / `runtime.memmove` calls | 15 / 15 |
| receiver register after makeslice | rdx: 15 |
| receiver register after memmove | rdx: 14, rax: 1 (SyncCommitteeMessage.BlockRoot) |
| distinct set-up sequences (displacements abstracted) | 19: callee 8, makeslice 8, memmove 3 |
| directive forms in set-ups | `mov %r,d(%rsp)`, `mov d(%rsp),%r`, `mov %r1,%r2`, `mov d(%r1),%r2`, `mov %r1,d(%r2)`, `lea d(%r1),%r2`, `add $imm,%r`, `mov $imm,%e..`, `nop`, `test %al,(%rax)` (heads only), and the fixed makeslice arguments `lea type(%rip),%rax; xor %ebx,%ebx` |
| prologue (directives 0–10) | the same shape in all 10; frame size, first spill displacement and SSZ size differ |

## Per decoder

### Checkpoint (108 directives)
- nop @8: after `mov %rbx,0x68(%rsp)` before `cmp $0x28,%rcx`
- nop @16: after `mov $0x8,%ecx` before `callq prim.Epoch.UnmarshalSSZ`
- nop @32: after `callq fmt.errorf` before `test %rax,%rax`
- nop @35: after `jne L_F_ae` before `lea type__+828672(%rip),%rax`
- nop @76: after `mov 0x38(%rsp),%rsi` before `jmp L_F_157`
- call @17 `prim.Epoch.UnmarshalSSZ` set-up @11..16: `mov %rax,0x60(%rsp); mov %rbx,0x68(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx; nop` | after: `test %rax,%rax; je L_F_b4; movups %xmm15,0x40(%rsp)`
- call @53 `runtime.makeslice` set-up @48..52: `mov %rbx,0x30(%rsp); mov %rax,0x28(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x60(%rsp),%rdx; movq $0x0,0x18(%rdx); movq $0x20,0x20(%rdx)`
- call @69 `runtime.memmove` set-up @64..68: `mov %rax,0x38(%rsp); mov %rax,0x10(%rdx); mov 0x68(%rsp),%rbx; add $0x8,%rbx; mov $0x20,%ecx` | after: `mov 0x60(%rsp),%rdx; movq $0x20,0x18(%rdx); movq $0x20,0x20(%rdx)`

### AttestationData (243 directives)
- nop @8: after `mov %rbx,0x88(%rsp)` before `cmp $0x80,%rcx`
- nop @34: after `jne L_F_c1` before `lea type__+828672(%rip),%rax`
- nop @36: after `lea type__+828672(%rip),%rax` before `callq runtime.newobject`
- nop @72: after `jne L_F_161` before `lea type__+828672(%rip),%rax`
- nop @74: after `lea type__+828672(%rip),%rax` before `callq runtime.newobject`
- nop @96: after `mov 0x18(%rdx),%rsi` before `callq runtime.gcWriteBarrier2`
- nop @125: after `cmpl $0x0,runtime.writeBarrier(%rip)` before `jne L_F_22c`
- nop @156: after `mov %rdi,%rsi` before `callq fmt.errorf`
- nop @160: after `jne L_F_2d3` before `lea type__+828672(%rip),%rax`
- nop @209: after `jne L_F_3a1` before `lea type__+828672(%rip),%rax`
- nop @211: after `lea type__+828672(%rip),%rax` before `callq runtime.newobject`
- call @17 `prim.Slot.UnmarshalSSZ` set-up @11..16: `mov %rax,0x80(%rsp); mov %rbx,0x88(%rsp); mov %rdi,0x98(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_c7; movups %xmm15,0x58(%rsp)`
- call @55 `prim.CommitteeIndex.UnmarshalSSZ` set-up @48..54: `mov 0x88(%rsp),%rbx; add $0x8,%rbx; mov 0x98(%rsp),%rdi; add $-0x8,%rdi; mov 0x80(%rsp),%rax; add $0x10,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_167; movups %xmm15,0x48(%rsp)`
- call @89 `runtime.makeslice` set-up @86..88: `lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x80(%rsp),%rdx; movq $0x0,0x20(%rdx); movq $0x20,0x28(%rdx)`
- call @106 `runtime.memmove` set-up @101..105: `mov %rax,0x68(%rsp); mov %rax,0x18(%rdx); mov 0x88(%rsp),%rbx; add $0x10,%rbx; mov $0x20,%ecx` | after: `mov 0x80(%rsp),%rdx; movq $0x20,0x20(%rdx); movq $0x20,0x28(%rdx)`
- call @142 `v1.Checkpoint.UnmarshalSSZ` set-up @136..141: `mov %rax,0x30(%rdx); mov 0x88(%rsp),%rbx; add $0x30,%rbx; mov 0x98(%rsp),%rdi; add $-0x30,%rdi; mov $0x28,%ecx` | after: `test %rax,%rax; je L_F_2d9; movups %xmm15,0x38(%rsp)`
- call @192 `v1.Checkpoint.UnmarshalSSZ` set-up @186..191: `mov %rax,0x38(%rdx); mov 0x88(%rsp),%rbx; add $0x58,%rbx; mov 0x98(%rsp),%rdi; add $-0x58,%rdi; mov $0x28,%ecx` | after: `test %rax,%rax; je L_F_3a7; movups %xmm15,0x28(%rsp)`

### BeaconBlockHeader (217 directives)
- nop @8: after `mov %rbx,0x78(%rsp)` before `cmp $0x70,%rcx`
- nop @34: after `jne L_F_b3` before `lea type__+828672(%rip),%rax`
- nop @54: after `mov $0x8,%ecx` before `callq prim.ValidatorIndex.UnmarshalSSZ`
- nop @70: after `callq fmt.errorf` before `test %rax,%rax`
- nop @73: after `jne L_F_14e` before `lea type__+828672(%rip),%rax`
- nop @114: after `mov 0x38(%rsp),%rdi` before `jmp L_F_1f7`
- nop @188: after `mov 0x48(%rdx),%rcx` before `callq runtime.gcWriteBarrier2`
- call @17 `prim.Slot.UnmarshalSSZ` set-up @11..16: `mov %rax,0x70(%rsp); mov %rdi,0x88(%rsp); mov %rbx,0x78(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_b9; movups %xmm15,0x50(%rsp)`
- call @55 `prim.ValidatorIndex.UnmarshalSSZ` set-up @47..54: `mov 0x78(%rsp),%rbx; add $0x8,%rbx; mov 0x88(%rsp),%rdi; add $-0x8,%rdi; mov 0x70(%rsp),%rax; add $0x10,%rax; mov $0x8,%ecx; nop` | after: `test %rax,%rax; je L_F_154; movups %xmm15,0x40(%rsp)`
- call @91 `runtime.makeslice` set-up @86..90: `mov %rbx,0x30(%rsp); mov %rax,0x28(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x0,0x20(%rdx); movq $0x20,0x28(%rdx)`
- call @107 `runtime.memmove` set-up @102..106: `mov %rax,0x38(%rsp); mov %rax,0x18(%rdx); mov 0x78(%rsp),%rbx; add $0x10,%rbx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x20,0x20(%rdx); movq $0x20,0x28(%rdx)`
- call @127 `runtime.makeslice` set-up @123..126: `mov %rdi,0x18(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x0,0x38(%rdx); movq $0x20,0x40(%rdx)`
- call @143 `runtime.memmove` set-up @138..142: `mov %rax,0x38(%rsp); mov %rax,0x30(%rdx); mov 0x78(%rsp),%rbx; add $0x30,%rbx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x20,0x38(%rdx); movq $0x20,0x40(%rdx)`
- call @162 `runtime.makeslice` set-up @158..161: `mov %rdi,0x30(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x0,0x50(%rdx); movq $0x20,0x58(%rdx)`
- call @178 `runtime.memmove` set-up @173..177: `mov %rax,0x38(%rsp); mov %rax,0x48(%rdx); mov 0x78(%rsp),%rbx; add $0x50,%rbx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x20,0x50(%rdx); movq $0x20,0x58(%rdx)`

### Eth1Data (108 directives)
- nop @8: after `mov %rbx,0x38(%rsp)` before `cmp $0x48,%rcx`
- nop @79: after `mov 0x28(%rdx),%rcx` before `callq runtime.gcWriteBarrier2`
- call @16 `runtime.makeslice` set-up @11..15: `mov %rax,0x30(%rsp); mov %rbx,0x38(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x10(%rdx); movq $0x20,0x18(%rdx)`
- call @31 `runtime.memmove` set-up @27..30: `mov %rax,0x18(%rsp); mov %rax,0x8(%rdx); mov 0x38(%rsp),%rbx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x20,0x10(%rdx); movq $0x20,0x18(%rdx)`
- call @53 `runtime.makeslice` set-up @46..52: `mov %rdi,0x8(%rdx); mov 0x38(%rsp),%rsi; mov 0x20(%rsi),%rsi; mov %rsi,0x20(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x30(%rdx); movq $0x20,0x38(%rdx)`
- call @69 `runtime.memmove` set-up @64..68: `mov %rax,0x18(%rsp); mov %rax,0x28(%rdx); mov 0x38(%rsp),%rbx; add $0x28,%rbx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x20,0x30(%rdx); movq $0x20,0x38(%rdx)`

### BlobIdentifier (72 directives)
- nop @8: after `mov %rbx,0x38(%rsp)` before `cmp $0x28,%rcx`
- call @16 `runtime.makeslice` set-up @11..15: `mov %rax,0x30(%rsp); mov %rbx,0x38(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x10(%rdx); movq $0x20,0x18(%rdx)`
- call @31 `runtime.memmove` set-up @27..30: `mov %rax,0x18(%rsp); mov %rax,0x8(%rdx); mov 0x38(%rsp),%rbx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x20,0x10(%rdx); movq $0x20,0x18(%rdx)`

### DepositMessage (109 directives)
- nop @8: after `mov %rbx,0x38(%rsp)` before `cmp $0x58,%rcx`
- nop @57: after `mov 0x18(%rdx),%rsi` before `callq runtime.gcWriteBarrier2`
- nop @107: after `mov 0x20(%rsp),%rdi` before `jmpq L_F_0`
- call @16 `runtime.makeslice` set-up @11..15: `mov %rax,0x30(%rsp); mov %rbx,0x38(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x30,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x8(%rdx); movq $0x30,0x10(%rdx)`
- call @31 `runtime.memmove` set-up @27..30: `mov %rax,0x18(%rsp); mov %rax,(%rdx); mov 0x38(%rsp),%rbx; mov $0x30,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x30,0x8(%rdx); movq $0x30,0x10(%rdx)`
- call @50 `runtime.makeslice` set-up @46..49: `mov %rdi,(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x20(%rdx); movq $0x20,0x28(%rdx)`
- call @67 `runtime.memmove` set-up @62..66: `mov %rax,0x18(%rsp); mov %rax,0x18(%rdx); mov 0x38(%rsp),%rbx; add $0x30,%rbx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x20,0x20(%rdx); movq $0x20,0x28(%rdx)`

### Deposit_Data (143 directives)
- nop @8: after `mov %rbx,0x38(%rsp)` before `cmp $0xb8,%rcx`
- nop @50: after `mov $0x20,%ecx` before `callq runtime.makeslice`
- call @16 `runtime.makeslice` set-up @11..15: `mov %rax,0x30(%rsp); mov %rbx,0x38(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x30,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x10(%rdx); movq $0x30,0x18(%rdx)`
- call @31 `runtime.memmove` set-up @27..30: `mov %rax,0x18(%rsp); mov %rax,0x8(%rdx); mov 0x38(%rsp),%rbx; mov $0x30,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x30,0x10(%rdx); movq $0x30,0x18(%rdx)`
- call @51 `runtime.makeslice` set-up @46..50: `mov %rdi,0x8(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx; nop` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x28(%rdx); movq $0x20,0x30(%rdx)`
- call @67 `runtime.memmove` set-up @62..66: `mov %rax,0x18(%rsp); mov %rax,0x20(%rdx); mov 0x38(%rsp),%rbx; add $0x30,%rbx; mov $0x20,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x20,0x28(%rdx); movq $0x20,0x30(%rdx)`
- call @89 `runtime.makeslice` set-up @82..88: `mov %rdi,0x20(%rdx); mov 0x38(%rsp),%rsi; mov 0x50(%rsi),%rsi; mov %rsi,0x38(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x60,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x0,0x48(%rdx); movq $0x60,0x50(%rdx)`
- call @105 `runtime.memmove` set-up @100..104: `mov %rax,0x18(%rsp); mov %rax,0x40(%rdx); mov 0x38(%rsp),%rbx; add $0x58,%rbx; mov $0x60,%ecx` | after: `mov 0x30(%rsp),%rdx; movq $0x60,0x48(%rdx); movq $0x60,0x50(%rdx)`

### PendingPartialWithdrawal (109 directives)
- nop @8: after `mov %rbx,0x60(%rsp)` before `cmp $0x18,%rcx`
- nop @31: after `mov %rdi,%rsi` before `callq fmt.errorf`
- nop @35: after `jne L_F_b3` before `lea type__+828672(%rip),%rax`
- nop @76: after `jne L_F_153` before `lea type__+828672(%rip),%rax`
- call @17 `prim.ValidatorIndex.UnmarshalSSZ` set-up @11..16: `mov %rax,0x58(%rsp); mov %rdi,0x70(%rsp); mov %rbx,0x60(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_b9; movups %xmm15,0x38(%rsp)`
- call @59 `prim.Epoch.UnmarshalSSZ` set-up @48..58: `mov 0x60(%rsp),%rbx; lea 0x10(%rbx),%rdx; mov 0x70(%rsp),%rdi; add $-0x10,%rdi; mov 0x58(%rsp),%rax; lea 0x18(%rax),%rsi; mov 0x8(%rbx),%r8; mov %r8,0x10(%rax); mov %rsi,%rax; mov %rdx,%rbx; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_159; movups %xmm15,0x28(%rsp)`

### PendingConsolidation (107 directives)
- nop @8: after `mov %rbx,0x60(%rsp)` before `cmp $0x10,%rcx`
- nop @31: after `mov %rdi,%rsi` before `callq fmt.errorf`
- nop @35: after `jne L_F_b3` before `lea type__+828672(%rip),%rax`
- nop @56: after `callq prim.ValidatorIndex.UnmarshalSSZ` before `test %rax,%rax`
- nop @73: after `jne L_F_147` before `lea type__+828672(%rip),%rax`
- nop @100: after `mov %rdi,0x20(%rsp)` before `callq runtime.morestack_noctxt.abi0`
- call @17 `prim.ValidatorIndex.UnmarshalSSZ` set-up @11..16: `mov %rax,0x58(%rsp); mov %rbx,0x60(%rsp); mov %rdi,0x70(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_b9; movups %xmm15,0x38(%rsp)`
- call @55 `prim.ValidatorIndex.UnmarshalSSZ` set-up @48..54: `mov 0x60(%rsp),%rbx; add $0x8,%rbx; mov 0x70(%rsp),%rdi; add $-0x8,%rdi; mov 0x58(%rsp),%rax; add $0x10,%rax; mov $0x8,%ecx` | after: `nop; test %rax,%rax; je L_F_14d`

### SyncCommitteeMessage (179 directives)
- nop @8: after `mov %rbx,0x78(%rsp)` before `cmp $0x90,%rcx`
- nop @34: after `jne L_F_b6` before `lea type__+828672(%rip),%rax`
- nop @105: after `jne L_F_1e1` before `lea type__+828672(%rip),%rax`
- nop @123: after `mov $0x60,%ecx` before `callq runtime.makeslice`
- nop @177: after `mov 0x20(%rsp),%rdi` before `jmpq L_F_0`
- call @17 `prim.Slot.UnmarshalSSZ` set-up @11..16: `mov %rax,0x70(%rsp); mov %rdi,0x88(%rsp); mov %rbx,0x78(%rsp); test %al,(%rax); add $0x8,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_bc; movups %xmm15,0x50(%rsp)`
- call @50 `runtime.makeslice` set-up @47..49: `lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x0,0x18(%rdx); movq $0x20,0x20(%rdx)`
- call @66 `runtime.memmove` set-up @61..65: `mov %rax,0x38(%rsp); mov %rax,0x10(%rdx); mov 0x78(%rsp),%rbx; add $0x8,%rbx; mov $0x20,%ecx` | after: `mov 0x70(%rsp),%rax; movq $0x20,0x18(%rax); movq $0x20,0x20(%rax)`
- call @88 `prim.ValidatorIndex.UnmarshalSSZ` set-up @81..87: `mov %rsi,0x10(%rax); mov 0x78(%rsp),%rbx; add $0x28,%rbx; mov 0x88(%rsp),%rdi; add $-0x28,%rdi; add $0x28,%rax; mov $0x8,%ecx` | after: `test %rax,%rax; je L_F_1e7; movups %xmm15,0x40(%rsp)`
- call @124 `runtime.makeslice` set-up @118..123: `mov %rbx,0x30(%rsp); mov %rax,0x28(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $0x60,%ecx; nop` | after: `mov 0x70(%rsp),%rdx; movq $0x0,0x38(%rdx); movq $0x60,0x40(%rdx)`
- call @140 `runtime.memmove` set-up @135..139: `mov %rax,0x38(%rsp); mov %rax,0x30(%rdx); mov 0x78(%rsp),%rbx; add $0x30,%rbx; mov $0x60,%ecx` | after: `mov 0x70(%rsp),%rdx; movq $0x60,0x38(%rdx); movq $0x60,0x40(%rdx)`

## Distinct set-up sequences (displacements abstracted to N) (displacements abstracted to N)
- [callee] `mov %rax,N(%rdx); mov N(%rsp),%rbx; add $N,%rbx; mov N(%rsp),%rdi; add $N,%rdi; mov $N,%ecx` : 2 (AttestationData@142, AttestationData@192)
- [callee] `mov %rax,N(%rsp); mov %rbx,N(%rsp); mov %rdi,N(%rsp); test %al,(%rax); add $N,%rax; mov $N,%ecx` : 2 (AttestationData@17, PendingConsolidation@17)
- [callee] `mov %rax,N(%rsp); mov %rbx,N(%rsp); test %al,(%rax); add $N,%rax; mov $N,%ecx; nop` : 1 (Checkpoint@17)
- [callee] `mov %rax,N(%rsp); mov %rdi,N(%rsp); mov %rbx,N(%rsp); test %al,(%rax); add $N,%rax; mov $N,%ecx` : 3 (BeaconBlockHeader@17, PendingPartialWithdrawal@17, SyncCommitteeMessage@17)
- [callee] `mov %rsi,N(%rax); mov N(%rsp),%rbx; add $N,%rbx; mov N(%rsp),%rdi; add $N,%rdi; add $N,%rax; mov $N,%ecx` : 1 (SyncCommitteeMessage@88)
- [callee] `mov N(%rsp),%rbx; add $N,%rbx; mov N(%rsp),%rdi; add $N,%rdi; mov N(%rsp),%rax; add $N,%rax; mov $N,%ecx` : 2 (AttestationData@55, PendingConsolidation@55)
- [callee] `mov N(%rsp),%rbx; add $N,%rbx; mov N(%rsp),%rdi; add $N,%rdi; mov N(%rsp),%rax; add $N,%rax; mov $N,%ecx; nop` : 1 (BeaconBlockHeader@55)
- [callee] `mov N(%rsp),%rbx; lea N(%rbx),%rdx; mov N(%rsp),%rdi; add $N,%rdi; mov N(%rsp),%rax; lea N(%rax),%rsi; mov N(%rbx),%r8; mov %r8,N(%rax); mov %rsi,%rax; mov %rdx,%rbx; mov $N,%ecx` : 1 (PendingPartialWithdrawal@59)
- [makeslice] `lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 2 (AttestationData@89, SyncCommitteeMessage@50)
- [makeslice] `mov %rax,N(%rsp); mov %rbx,N(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 4 (Eth1Data@16, BlobIdentifier@16, DepositMessage@16, Deposit_Data@16)
- [makeslice] `mov %rbx,N(%rsp); mov %rax,N(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 2 (Checkpoint@53, BeaconBlockHeader@91)
- [makeslice] `mov %rbx,N(%rsp); mov %rax,N(%rsp); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx; nop` : 1 (SyncCommitteeMessage@124)
- [makeslice] `mov %rdi,(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 1 (DepositMessage@50)
- [makeslice] `mov %rdi,N(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 2 (BeaconBlockHeader@127, BeaconBlockHeader@162)
- [makeslice] `mov %rdi,N(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx; nop` : 1 (Deposit_Data@51)
- [makeslice] `mov %rdi,N(%rdx); mov N(%rsp),%rsi; mov N(%rsi),%rsi; mov %rsi,N(%rdx); lea type__+387072(%rip),%rax; xor %ebx,%ebx; mov $N,%ecx` : 2 (Eth1Data@53, Deposit_Data@89)
- [memmove] `mov %rax,N(%rsp); mov %rax,(%rdx); mov N(%rsp),%rbx; mov $N,%ecx` : 1 (DepositMessage@31)
- [memmove] `mov %rax,N(%rsp); mov %rax,N(%rdx); mov N(%rsp),%rbx; add $N,%rbx; mov $N,%ecx` : 11 (Checkpoint@69, AttestationData@106, BeaconBlockHeader@107, BeaconBlockHeader@143, BeaconBlockHeader@178, Eth1Data@69, DepositMessage@67, Deposit_Data@67, Deposit_Data@105, SyncCommitteeMessage@66, SyncCommitteeMessage@140)
- [memmove] `mov %rax,N(%rsp); mov %rax,N(%rdx); mov N(%rsp),%rbx; mov $N,%ecx` : 3 (Eth1Data@31, BlobIdentifier@31, Deposit_Data@31)

nop sites total 46; receiver reload registers ['rax', 'rdx']; distinct set-ups 19
