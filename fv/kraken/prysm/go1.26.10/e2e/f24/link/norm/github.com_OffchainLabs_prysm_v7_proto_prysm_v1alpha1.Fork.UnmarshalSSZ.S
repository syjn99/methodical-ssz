github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1d5
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1c1
  mov %rax,0x48(%rsp)
  mov %rdi,0x60(%rsp)
  mov %rbx,0x50(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_7a:
  mov %rax,0x8(%rdx)
  mov 0x50(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_b2
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_b2:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_f7
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_f7:
  mov %rax,0x20(%rdx)
  mov 0x50(%rsp),%rbx
  mov 0x4(%rbx),%esi
  mov %esi,(%rax)
  movq $0x4,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_12e
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_12e:
  mov %rax,0x20(%rdx)
  add $0x8,%rbx
  mov 0x60(%rsp),%rdi
  add $-0x8,%rdi
  lea 0x38(%rdx),%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1ba
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_15e
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_15e:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+18159(%rip),%rax
  mov $0x9,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1b4
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18159(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1b4:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1ba:
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1c1:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1d5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_0
