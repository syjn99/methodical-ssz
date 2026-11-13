github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_201
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x40,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1ed
  mov %rax,0x60(%rsp)
  mov %rdi,0x78(%rsp)
  mov %rbx,0x68(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_b9
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_5a
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_5a:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+18141(%rip),%rax
  mov $0x9,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18141(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_b3:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_b9:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x30,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_fa
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_fa:
  mov %rax,0x28(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x30,0x18(%rax)
  movq $0x30,0x20(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_13b
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_151
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_13b:
  mov 0x10(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_151:
  mov %rsi,0x10(%rax)
  mov 0x68(%rsp),%rbx
  add $0x38,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x38,%rdi
  add $0x28,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1e7
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_186
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_186:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+46529(%rip),%rax
  mov $0x13,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x13,0x8(%rax)
  lea go_string._+46529(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1e1:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1e7:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_1ed:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_201:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.UnmarshalSSZ_0
