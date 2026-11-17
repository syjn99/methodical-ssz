github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_1a1
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_185
  mov %rax,0x90(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_7c
  mov %rcx,0xa0(%rsp)
  mov %rdx,0x78(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x78(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_7c:
  mov %rbx,0x70(%rsp)
  mov %r8,0x50(%rsp)
  mov %rdi,0x58(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  add $0x8,%rbx
  mov 0x90(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  mov 0x58(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_c2
  mov 0x70(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_ea
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_c2:
  mov %rsi,0x48(%rsp)
  mov 0x70(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_ea:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x28(%rdx),%r8
  cmpq $0x20,0x30(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_16a
  lea 0x20(%rbx),%rdx
  nop
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_132
  mov %rbx,0x40(%rsp)
  mov %r8,0x78(%rsp)
  mov %rdx,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x78(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_132:
  mov %rax,0x78(%rsp)
  mov %rdx,0x68(%rsp)
  mov %rcx,0x60(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x78(%rsp),%rax
  mov 0x68(%rsp),%rbx
  mov 0x60(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_16a:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_185:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_1a1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.MarshalSSZTo_0
