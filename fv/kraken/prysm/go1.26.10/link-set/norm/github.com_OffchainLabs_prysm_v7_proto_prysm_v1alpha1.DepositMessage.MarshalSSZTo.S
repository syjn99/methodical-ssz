github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_19e
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  mov (%rax),%rdx
  cmpq $0x30,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_183
  mov %rax,0x90(%rsp)
  lea 0x30(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_7b
  mov %rdx,0x78(%rsp)
  mov %rcx,0xa0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x78(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_7b:
  mov %rbx,0x78(%rsp)
  mov %r8,0x60(%rsp)
  mov %rdi,0x58(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x90(%rsp),%rdx
  mov 0x18(%rdx),%rbx
  cmpq $0x20,0x20(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_168
  mov 0x60(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x58(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_cc
  mov 0x78(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_f7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_cc:
  mov %rbx,0x70(%rsp)
  mov 0x78(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%r8
  mov %rbx,%r9
  mov 0x70(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_f7:
  mov %rax,0x68(%rsp)
  mov %r9,0x48(%rsp)
  mov %rcx,0x50(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  add $0x8,%rbx
  mov 0x90(%rsp),%rdx
  mov 0x30(%rdx),%rdx
  mov 0x50(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_139
  mov 0x68(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_159
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_139:
  mov %rdx,0x40(%rsp)
  mov 0x68(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_159:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_168:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_183:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_19e:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.MarshalSSZTo_0
