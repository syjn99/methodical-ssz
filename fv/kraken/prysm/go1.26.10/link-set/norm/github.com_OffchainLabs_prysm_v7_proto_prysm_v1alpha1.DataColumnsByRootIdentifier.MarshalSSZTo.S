github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_188
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_117
  mov %rax,0x90(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_7c
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_7c:
  mov %r8,0x48(%rsp)
  mov %rbx,0x68(%rsp)
  mov %rdi,0x50(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  add $0x4,%rbx
  nop
  mov 0x50(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_b7
  mov 0x68(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_cd
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_b7:
  mov 0x68(%rsp),%rax
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_cd:
  movl $0x24,-0x4(%rbx,%rax,1)
  mov 0x90(%rsp),%rdx
  mov 0x28(%rdx),%r8
  cmp $0x80,%r8
  jg L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_fc
  mov %r8,0x60(%rsp)
  mov 0x20(%rdx),%rdx
  mov %rdx,0x70(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_13a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_fc:
  mov ssz.ErrListTooBig(%rip),%rdi
  mov ssz.ErrListTooBig+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_117:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_132:
  mov %r9,-0x8(%rbx,%rax,1)
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_13a:
  cmp %r8,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_17e
  add $0x8,%rbx
  mov (%rdx,%rsi,8),%r9
  nop
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_132
  mov %rsi,0x58(%rsp)
  mov %r9,0x40(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x70(%rsp),%rdx
  mov 0x58(%rsp),%rsi
  mov 0x60(%rsp),%r8
  mov 0x40(%rsp),%r9
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_132
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_17e:
  xor %edi,%edi
  xor %esi,%esi
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_188:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.MarshalSSZTo_0
