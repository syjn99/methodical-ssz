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
