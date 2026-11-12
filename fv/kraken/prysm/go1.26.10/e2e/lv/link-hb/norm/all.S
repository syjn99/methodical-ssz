github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2b0
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x80000,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_7b
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x2000,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x2000,0x8(%rdx)
  movq $0x2000,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_74:
  mov %rax,(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_a0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_7b:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f:
  mov %r9,(%rdi,%rsi,8)
  mov 0x18(%rsp),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_a0:
  cmp $0x2000,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_166
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2aa
  mov %rsi,0x28(%rsp)
  mov %rax,0x20(%rsp)
  mov %r8,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x30(%rsp)
  mov 0x20(%rsp),%rdx
  mov 0x50(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rdx
  mov 0x8(%rdx),%rsi
  mov 0x28(%rsp),%rdi
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2a5
  lea (%rdi,%rdi,2),%rsi
  mov (%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_14c
  mov 0x30(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_14c:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x30(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_166:
  lea type__+337600(%rip),%rax
  mov $0x2000,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x2000,0x20(%rdx)
  movq $0x2000,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1ac
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1ac:
  mov %rax,0x18(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1c0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4:
  mov %r9,(%rdi,%rsi,8)
  mov 0x18(%rsp),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1c0:
  cmp $0x2000,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_28c
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_29b
  mov %rsi,0x28(%rsp)
  mov %rax,0x20(%rsp)
  mov %r8,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x30(%rsp)
  mov 0x20(%rsp),%rdx
  mov 0x50(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  lea 0x40000(%rbx),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  mov 0x28(%rsp),%rdi
  nop
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_296
  lea (%rdi,%rdi,2),%rsi
  mov 0x18(%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_272
  mov 0x30(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_272:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x30(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_28c:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_296:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_29b:
  nop
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2a5:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2aa:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2b0:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_0
