github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_0:
  lea 0xffffff58(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_39f
  push %rbp
  mov %rsp,%rbp
  sub $0x120,%rsp
  mov %rbx,0x138(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_381
  mov %rax,0x130(%rsp)
  lea 0x30(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_88
  mov %rcx,0x140(%rsp)
  mov %rdx,0x118(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x118(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x140(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_88:
  mov %rdi,0x80(%rsp)
  mov %r8,0x78(%rsp)
  mov %rbx,0x118(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x130(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_363
  mov 0x78(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x80(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_e6
  mov 0x118(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_11a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_e6:
  mov %rbx,0x110(%rsp)
  mov 0x118(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x78(%rsp),%r8
  mov %rbx,%r9
  mov 0x110(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_11a:
  mov %rcx,0x70(%rsp)
  mov %r9,0x68(%rsp)
  mov %rax,0x108(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov 0x130(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x70(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_162
  mov 0x108(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_192
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_162:
  mov %rsi,0x58(%rsp)
  mov 0x108(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
  mov 0x58(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_192:
  mov %rsi,-0x8(%rbx,%rax,1)
  cmpb $0x0,0x40(%rdx)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1c5
  inc %rbx
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1be
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1be:
  movb $0x1,-0x1(%rbx,%rax,1)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1eb
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1c5:
  inc %rbx
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1e6
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1e6:
  movb $0x0,-0x1(%rbx,%rax,1)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_1eb:
  lea 0x8(%rbx),%r8
  mov 0x48(%rdx),%r9
  nop
  nop
  lea 0xe8(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0xe8(%rsp)
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_23c
  mov %rbx,0x60(%rsp)
  mov %r8,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
  mov %rbx,%r8
  mov 0x60(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_23c:
  mov 0xe8(%rsp),%r9
  mov %r9,(%rax,%rbx,1)
  lea 0x8(%r8),%rbx
  mov 0x50(%rdx),%r9
  nop
  nop
  nop
  lea 0xc8(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0xc8(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_294
  mov %r8,0x50(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
  mov 0x50(%rsp),%r8
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_294:
  mov 0xc8(%rsp),%r9
  mov %r9,(%rax,%r8,1)
  lea 0x8(%rbx),%r8
  mov 0x58(%rdx),%r9
  nop
  nop
  nop
  lea 0xa8(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0xa8(%rsp)
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_2f5
  mov %rbx,0x48(%rsp)
  mov %r8,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x130(%rsp),%rdx
  mov %rbx,%r8
  mov 0x48(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_2f5:
  mov 0xa8(%rsp),%r9
  mov %r9,(%rax,%rbx,1)
  lea 0x8(%r8),%rbx
  mov 0x60(%rdx),%rdx
  nop
  nop
  nop
  lea 0x88(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %rdx,0x88(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_34a
  mov %r8,0x40(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x40(%rsp),%r8
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_34a:
  mov 0x88(%rsp),%rdx
  mov %rdx,(%rax,%r8,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0x120,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_363:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x120,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_381:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x120,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_39f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.MarshalSSZTo_0
