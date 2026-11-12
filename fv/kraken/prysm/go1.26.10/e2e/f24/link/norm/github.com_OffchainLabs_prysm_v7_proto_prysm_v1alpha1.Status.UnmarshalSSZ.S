github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_32e
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x54,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_31a
  mov %rax,0x60(%rsp)
  mov %rdi,0x78(%rsp)
  mov %rbx,0x68(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_7a:
  mov %rax,0x8(%rdx)
  mov 0x68(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_b2
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_b2:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_f7
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_f7:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x4,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x20,0x28(%rax)
  movq $0x20,0x30(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_138
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_151
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_138:
  mov 0x20(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_151:
  mov %rsi,0x20(%rax)
  mov 0x68(%rsp),%rbx
  add $0x24,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x24,%rdi
  add $0x38,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e7
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_186
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_186:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43515(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43515(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e1:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e7:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x20,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_22c
  mov 0x40(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_22c:
  mov %rax,0x28(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x2c,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x20,0x48(%rax)
  movq $0x20,0x50(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_26d
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_282
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_26d:
  mov 0x40(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_282:
  mov %rsi,0x40(%rax)
  mov 0x68(%rsp),%rbx
  add $0x4c,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x4c,%rdi
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_314
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_2b7
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_2b7:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+26459(%rip),%rax
  mov $0xc,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_30e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xc,0x8(%rax)
  lea go_string._+26459(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_30e:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_314:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_31a:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_32e:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_0
