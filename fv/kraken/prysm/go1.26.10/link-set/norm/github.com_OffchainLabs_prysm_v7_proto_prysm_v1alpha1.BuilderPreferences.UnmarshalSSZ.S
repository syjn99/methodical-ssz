github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_c1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_ad
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Gwei.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_a7
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_4b
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_4b:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+58620(%rip),%rax
  mov $0x17,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_a1
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x17,0x8(%rax)
  lea go_string._+58620(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_a1:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_a7:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_ad:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_c1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.UnmarshalSSZ_0
