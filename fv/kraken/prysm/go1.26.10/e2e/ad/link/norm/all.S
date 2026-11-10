github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_cc
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x8,%rcx
  je L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_bb
  lea 0x28(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  lea type__+387520(%rip),%rdx
  mov %rdx,0x28(%rsp)
  lea runtime.gcbits._+1432(%rip),%rdx
  mov %rdx,0x30(%rsp)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x38(%rsp)
  mov %rax,0x40(%rsp)
  lea go_string._+110097(%rip),%rax
  mov $0x28,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_b5
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x28,0x8(%rax)
  lea go_string._+110097(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_b5:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_bb:
  mov (%rbx),%rcx
  nop
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_cc:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_7d
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  nop
  nop
  lea 0x28(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x28(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_61
  mov %rcx,0x68(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov 0x68(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_61:
  mov 0x28(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_7d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZ_4a
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov (%rax),%rdx
  mov %rdx,0x40(%rsp)
  lea runtime.zerobase(%rip),%rax
  mov $0x8,%ebx
  xor %ecx,%ecx
  mov %rbx,%rdi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rdx,(%rax)
  mov $0x8,%ebx
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZ_4a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.MarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.SizeSSZ:
  mov $0x8,%eax
  retq
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_cc
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x8,%rcx
  je L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb
  lea 0x28(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  lea type__+387520(%rip),%rdx
  mov %rdx,0x28(%rsp)
  lea runtime.gcbits._+1432(%rip),%rdx
  mov %rdx,0x30(%rsp)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x38(%rsp)
  mov %rax,0x40(%rsp)
  lea go_string._+110057(%rip),%rax
  mov $0x28,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_b5
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x28,0x8(%rax)
  lea go_string._+110057(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_b5:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_bb:
  mov (%rbx),%rcx
  nop
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_cc:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_7d
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  lea 0x8(%rcx),%rdx
  mov (%rax),%r8
  nop
  nop
  lea 0x28(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x28(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_61
  mov %rcx,0x68(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov 0x68(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_61:
  mov 0x28(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_7d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ_4a
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov (%rax),%rdx
  mov %rdx,0x40(%rsp)
  lea runtime.zerobase(%rip),%rax
  mov $0x8,%ebx
  xor %ecx,%ecx
  mov %rbx,%rdi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rdx,(%rax)
  mov $0x8,%ebx
  xor %edi,%edi
  xor %esi,%esi
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ_4a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.MarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.SizeSSZ:
  mov $0x8,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.SizeSSZ:
  mov $0x80,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_0:
  lea -0x38(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_39f
  push %rbp
  mov %rsp,%rbp
  sub $0xb0,%rsp
  mov %rbx,0xc8(%rsp)
  mov %rax,0xc0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x68(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x68(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_88
  mov %rcx,0xd0(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xd0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xc0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_88:
  mov 0x68(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x48(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x48(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_e9
  mov %rdx,0x30(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
  mov 0xc0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_e9:
  mov 0x48(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x20,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_381
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_14c
  mov %r8,0x28(%rsp)
  mov %rdx,0x88(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x88(%rsp),%rdx
  mov 0x28(%rsp),%r8
  mov %rbx,%r9
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_14c:
  mov %rbx,0x88(%rsp)
  mov %r9,0x40(%rsp)
  mov %rdi,0x38(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xc0(%rsp),%rdx
  cmpq $0x0,0x30(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1b9
  lea type__+1289312(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_19d
  mov 0xc0(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1b5
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_19d:
  mov 0xc0(%rsp),%rdx
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1b5:
  mov %rax,0x30(%rdx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1b9:
  mov 0x30(%rdx),%rax
  mov 0x88(%rsp),%rbx
  mov 0x40(%rsp),%rcx
  mov 0x38(%rsp),%rdi
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo
  test %rdi,%rdi
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_264
  movups %xmm15,0xa0(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1ec
  mov 0x8(%rdi),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_1ec:
  mov %rdi,0xa0(%rsp)
  mov %rsi,0xa8(%rsp)
  lea go_string._+21316(%rip),%rax
  mov $0xa,%ebx
  lea 0xa0(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_24e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+21316(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_24e:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_264:
  mov 0xc0(%rsp),%rdx
  cmpq $0x0,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2d2
  mov %rax,0x88(%rsp)
  mov %rcx,0x40(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+1289312(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2a4
  mov 0xc0(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2bc
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2a4:
  mov 0xc0(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2bc:
  mov %rax,0x38(%rdx)
  mov 0x88(%rsp),%rax
  mov 0x40(%rsp),%rcx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2d2:
  mov 0x38(%rdx),%rdx
  mov %rcx,%rdi
  mov %rbx,%rcx
  mov %rax,%rbx
  mov %rdx,%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo
  test %rdi,%rdi
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_377
  movups %xmm15,0x90(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2ff
  mov 0x8(%rdi),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_2ff:
  mov %rdi,0x90(%rsp)
  mov %rsi,0x98(%rsp)
  lea go_string._+21326(%rip),%rax
  mov $0xa,%ebx
  lea 0x90(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_361
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+21326(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_361:
  xor %ecx,%ecx
  mov %rax,%rdi
  mov %rbx,%rsi
  xor %eax,%eax
  mov %rcx,%rbx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_377:
  add $0xb0,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_381:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_39f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3c1
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  nop
  cmp $0x80,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3ad
  mov %rax,0x80(%rsp)
  mov %rbx,0x88(%rsp)
  mov %rdi,0x98(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7
  movups %xmm15,0x58(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_66
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_66:
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x58(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c1:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_c7:
  mov 0x88(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x80(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_106
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_106:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+43533(%rip),%rax
  mov $0x12,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43533(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_161:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_167:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1ac
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1ac:
  mov %rax,0x68(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x10,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1f3
  mov 0x68(%rsp),%rbx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_208
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_1f3:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x68(%rsp),%rbx
  mov %rbx,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_208:
  mov %rbx,0x18(%rdx)
  lea type__+1289312(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_22c
  mov 0x80(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_244
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_22c:
  mov 0x80(%rsp),%rdx
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_244:
  mov %rax,0x30(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x30,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x30,%rdi
  mov $0x28,%ecx
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2d9
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_27b
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_27b:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+21316(%rip),%rax
  mov $0xa,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2d3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+21316(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2d3:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2d9:
  lea type__+1289312(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2f8
  mov 0x80(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_310
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_2f8:
  mov 0x80(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_310:
  mov %rax,0x38(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x58,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x58,%rdi
  mov $0x28,%ecx
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3a7
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_347
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_347:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+21326(%rip),%rax
  mov $0xa,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3a1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+21326(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3a1:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3a7:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3ad:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_3c1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ_0
