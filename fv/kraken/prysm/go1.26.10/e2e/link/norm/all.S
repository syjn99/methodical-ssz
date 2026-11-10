github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_cc
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x8,%rcx
  je L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_bb
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
  jne L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_b5
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x28,0x8(%rax)
  lea go_string._+110057(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_b5:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_bb:
  mov (%rbx),%rcx
  nop
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_cc:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_7d
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
  jae L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_61
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
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_61:
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
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_7d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_4a
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
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_4a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.MarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.SizeSSZ:
  mov $0x8,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.SizeSSZ:
  mov $0x28,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_123
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x30(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x30(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_7b
  mov %rax,0x78(%rsp)
  mov %rcx,0x88(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
  mov 0x78(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_7b:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x20,0x18(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_108
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf
  mov %rdx,0x28(%rsp)
  mov %r8,0x60(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov 0x60(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_cf:
  mov %rdi,0x58(%rsp)
  mov %r9,0x50(%rsp)
  mov %rbx,0x60(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  mov 0x50(%rsp),%rbx
  mov 0x58(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_108:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_123:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_17f
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x28,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_16b
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_56:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+18159(%rip),%rax
  mov $0x9,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18159(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_ae:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_b4:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_ff
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_ff:
  mov %rax,0x38(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  movq $0x20,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_142
  mov 0x38(%rsp),%rsi
  nop
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_157
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_142:
  mov 0x10(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_157:
  mov %rsi,0x10(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_16b:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_17f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.UnmarshalSSZ_0
