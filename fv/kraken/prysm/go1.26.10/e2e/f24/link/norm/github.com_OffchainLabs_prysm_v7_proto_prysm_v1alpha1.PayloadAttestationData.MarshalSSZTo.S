github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1cf
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1b4
  mov %rax,0x90(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_7c
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_7c:
  mov %rdi,0x48(%rsp)
  mov %r8,0x40(%rsp)
  mov %rbx,0x70(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0x90(%rsp),%rsi
  mov 0x20(%rsi),%rdi
  nop
  nop
  nop
  lea 0x50(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x50(%rsp)
  mov 0x48(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_d8
  mov 0x70(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_101
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_d8:
  mov 0x70(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_101:
  mov 0x50(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  cmpb $0x0,0x28(%rsi)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_139
  lea 0x1(%rdx),%rbx
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_132
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_132:
  movb $0x1,-0x1(%rbx,%rax,1)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_163
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_139:
  lea 0x1(%rdx),%rbx
  nop
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_15e
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_15e:
  movb $0x0,-0x1(%rbx,%rax,1)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_163:
  cmpb $0x0,0x29(%rsi)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_18c
  inc %rbx
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_185
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_185:
  movb $0x1,-0x1(%rbx,%rax,1)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1aa
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_18c:
  inc %rbx
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1a5
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1a5:
  movb $0x0,-0x1(%rbx,%rax,1)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1aa:
  xor %edi,%edi
  xor %esi,%esi
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1b4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_1cf:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.MarshalSSZTo_0
