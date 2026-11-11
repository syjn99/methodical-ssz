github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_18b
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xa0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_177
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x40,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x40,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x40,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x40,0x10(%rdx)
  movq $0x40,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x40,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_154
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_177:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_18b:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  nop
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_206
  push %rbp
  mov %rsp,%rbp
  sub $0x30,%rsp
  mov %rbx,0x48(%rsp)
  nop
  cmp $0x6030,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_7d
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x200,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x40(%rsp),%rdx
  movq $0x200,0x10(%rdx)
  movq $0x200,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_75:
  mov %rax,0x8(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_a0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_7d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x30,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91:
  mov %r10,(%rsi,%r8,8)
  lea 0x1(%rdi),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_a0:
  cmp $0x200,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_156
  mov %rax,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  nop
  callq runtime.makeslice
  mov %rax,0x28(%rsp)
  mov 0x18(%rsp),%rdx
  lea (%rdx,%rdx,2),%rdx
  mov %rdx,0x20(%rsp)
  shl $0x4,%rdx
  mov 0x48(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  mov 0x18(%rsp),%rdi
  nop
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1ff
  mov 0x8(%rdx),%rsi
  mov 0x20(%rsp),%r8
  movq $0x30,0x8(%rsi,%r8,8)
  movq $0x30,0x10(%rsi,%r8,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_137
  mov 0x28(%rsp),%r10
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_137:
  mov (%rsi,%r8,8),%r9
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%r10
  mov %r10,(%r11)
  mov %r9,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_156:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x40(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x48(%rsp),%rbx
  add $0x6000,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1db
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1db:
  mov 0x20(%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x30,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1ff:
  nop
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_206:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_47b
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  cmp $0xe4,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_268
  mov (%rbx),%edx
  nop
  nop
  nop
  nop
  cmp $0xe4,%rdx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_251
  lea -0xe4(%rdi),%rdx
  mov %rdx,%rsi
  neg %rdx
  sar $0x3f,%rdx
  and $0xe4,%edx
  add $-0xe4,%rcx
  add %rbx,%rdx
  test $0x7,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1a2
  shr $0x3,%rcx
  nop
  cmp $0x800,%rcx
  jg L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_105
  mov %rax,0xb8(%rsp)
  mov %rdi,0xd0(%rsp)
  mov %rsi,0x38(%rsp)
  mov %rdx,0x40(%rsp)
  mov %rcx,0x28(%rsp)
  mov %rbx,0xc0(%rsp)
  lea type__+387456(%rip),%rax
  mov %rcx,%rbx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  mov 0xb8(%rsp),%rsi
  mov %rdx,0x10(%rsi)
  mov %rdx,0x18(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_ed
  mov 0x8(%rsi),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_ed:
  mov %rax,0x8(%rsi)
  mov 0x38(%rsp),%rcx
  mov 0x40(%rsp),%rbx
  xor %eax,%eax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_28a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_105:
  lea 0x60(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x60(%rsp)
  mov %rax,0x68(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_13c
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_13c:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0x70(%rsp)
  mov %rdx,0x78(%rsp)
  lea go_string._+163839(%rip),%rax
  mov $0x49,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_199
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x49,0x8(%rax)
  lea go_string._+163839(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_199:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1a2:
  lea 0x80(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x80(%rsp)
  mov %rax,0x88(%rsp)
  mov ssz.ErrIncorrectListSize(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1e2
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1e2:
  mov ssz.ErrIncorrectListSize+8(%rip),%rdx
  mov %rcx,0x90(%rsp)
  mov %rdx,0x98(%rsp)
  lea go_string._+171319(%rip),%rax
  mov $0x53,%ebx
  lea 0x80(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_248
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x53,0x8(%rax)
  lea go_string._+171319(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_248:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_251:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_268:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_27f:
  mov 0x8(%rsi),%rdi
  mov %r10,(%rdi,%r9,8)
  mov %r8,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_28a:
  cmp %rdx,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2cc
  lea 0x1(%rax),%rdi
  mov %rdi,%r8
  shl $0x3,%rdi
  nop
  cmp %rcx,%rdi
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_475
  mov %rax,%r9
  shl $0x3,%rax
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_470
  mov 0x10(%rsi),%rdi
  nop
  mov (%rbx,%r9,8),%r10
  cmp %rdi,%r9
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_27f
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_46b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2cc:
  lea type__+1464512(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2ec
  mov 0xb8(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_304
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2ec:
  mov 0xb8(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_304:
  mov %rax,0x20(%rdx)
  mov 0xc0(%rsp),%rbx
  add $0x4,%rbx
  mov 0xd0(%rsp),%rdi
  add $-0x4,%rdi
  mov $0x80,%ecx
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_39c
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_33b
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_33b:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+15010(%rip),%rax
  mov $0x8,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_393
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+15010(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_393:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_39c:
  mov %rbx,0x48(%rsp)
  mov %rax,0x30(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0xb8(%rsp),%rdx
  movq $0x0,0x30(%rdx)
  movq $0x60,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_3ec
  mov 0x28(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_3ec:
  mov %rax,0xa0(%rsp)
  mov %rax,0x28(%rdx)
  mov 0xc0(%rsp),%rbx
  add $0x84,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0xb8(%rsp),%rdx
  movq $0x60,0x30(%rdx)
  movq $0x60,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_43c
  mov 0xa0(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_454
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_43c:
  mov 0x28(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0xa0(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_454:
  mov %rsi,0x28(%rdx)
  mov 0x30(%rsp),%rax
  mov 0x48(%rsp),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_46b:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_470:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_475:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_47b:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_0
