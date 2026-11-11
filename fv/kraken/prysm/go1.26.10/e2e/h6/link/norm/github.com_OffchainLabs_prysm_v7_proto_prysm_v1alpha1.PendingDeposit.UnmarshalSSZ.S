github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ce
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rbx,0x58(%rsp)
  nop
  cmp $0xc0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ba
  mov %rax,0x50(%rsp)
  mov %rdi,0x68(%rsp)
  mov %rbx,0x58(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_7d:
  mov %rax,0x28(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x58(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_ba
  mov 0x28(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_ba:
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_d1:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_116
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_116:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x58(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_157
  mov 0x28(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_171
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_157:
  mov 0x20(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_171:
  mov %rdi,0x20(%rdx)
  mov 0x58(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_1c3
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_1c3:
  mov %rax,0x28(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x58(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rax
  movq $0x60,0x48(%rax)
  movq $0x60,0x50(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_204
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_219
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_204:
  mov 0x40(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_219:
  mov %rsi,0x40(%rax)
  mov 0x58(%rsp),%rbx
  add $0xb8,%rbx
  mov 0x68(%rsp),%rdi
  add $-0xb8,%rdi
  add $0x58,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2b4
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_256
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_256:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ae:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2b4:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ba:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ce:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_0
