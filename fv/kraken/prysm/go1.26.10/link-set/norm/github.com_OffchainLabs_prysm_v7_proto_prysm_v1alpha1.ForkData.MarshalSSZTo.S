github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_15e
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  mov (%rax),%rdx
  cmpq $0x4,0x8(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_143
  lea 0x4(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_70
  mov %rax,0x58(%rsp)
  mov %rcx,0x68(%rsp)
  mov %rdx,0x40(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x68(%rsp),%rcx
  mov %rax,%rbx
  mov 0x58(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_70:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x20,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_128
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_c6
  mov %rdx,0x40(%rsp)
  mov %r8,0x38(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov 0x38(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_c6:
  mov %r9,0x38(%rsp)
  mov %rdi,0x30(%rsp)
  mov %rbx,0x40(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x58(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_10f
  mov 0x38(%rsp),%rbx
  mov 0x30(%rsp),%rcx
  mov 0x40(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_10f:
  mov $0x1,%eax
  mov 0x38(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_11e:
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_128:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_143:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_15e:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.MarshalSSZTo_0
