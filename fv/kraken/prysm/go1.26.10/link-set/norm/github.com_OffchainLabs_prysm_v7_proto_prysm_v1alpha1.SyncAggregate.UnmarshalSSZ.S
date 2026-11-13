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
