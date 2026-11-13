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
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_cc
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x8,%rcx
  je L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_bb
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
  jne L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_b5
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x28,0x8(%rax)
  lea go_string._+110057(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_b5:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_bb:
  mov (%rbx),%rcx
  nop
  mov %rcx,(%rax)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_cc:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_7d
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
  jae L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_61
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
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_61:
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
L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_7d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_261
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_243
  mov %rax,0x98(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_88
  mov %rcx,0xa8(%rsp)
  mov %rdx,0x80(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_88:
  mov %rbx,0x80(%rsp)
  mov %r8,0x68(%rsp)
  mov %rdi,0x60(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x98(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_225
  mov 0x68(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x60(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_e3
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_112
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_e3:
  mov %rbx,0x78(%rsp)
  mov 0x80(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x68(%rsp),%r8
  mov %rbx,%r9
  mov 0x78(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_112:
  mov %rax,0x70(%rsp)
  mov %r9,0x50(%rsp)
  mov %rcx,0x58(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x58(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_154
  mov 0x70(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_17c
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_154:
  mov %rsi,0x48(%rsp)
  mov 0x70(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_17c:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_207
  lea 0x60(%rbx),%rdx
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_1c6
  mov %r8,0x80(%rsp)
  mov %rbx,0x40(%rsp)
  mov %rdx,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_1c6:
  mov %rax,0x80(%rsp)
  mov %rdx,0x68(%rsp)
  mov %rcx,0x60(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  mov 0x68(%rsp),%rbx
  mov 0x60(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_207:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_225:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_243:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_261:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_233
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xb8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_21f
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_154
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_169:
  mov %rdi,0x20(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1bb
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1bb:
  mov %rax,0x18(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1fc
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_211
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1fc:
  mov 0x40(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_211:
  mov %rsi,0x40(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_21f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_233:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_17d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_162
  mov %rax,0x60(%rsp)
  lea 0x14(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_6b:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x48(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x30,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_147
  mov 0x30(%rsp),%rdx
  lea 0x30(%rdx),%r8
  mov 0x38(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  add %rdx,%rax
  mov $0x30,%ecx
  nop
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_12e
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_13d
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_12e:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_13d:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_147:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_162:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_17d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_184
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x44,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_170
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_10c
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x14,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_14d:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_162:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_170:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_184:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderExitRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_20d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1f2
  mov %rax,0x60(%rsp)
  lea 0x14(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_6b:
  mov %rbx,0x48(%rsp)
  mov %r8,0x38(%rsp)
  mov %rdi,0x30(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x30,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1d7
  mov 0x38(%rsp),%r8
  lea 0x30(%r8),%r9
  mov 0x30(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r9,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %r9,0x38(%rsp)
  mov %rcx,0x30(%rsp)
  add %r8,%rax
  mov $0x30,%ecx
  nop
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x38(%rdx),%rbx
  cmpq $0x30,0x40(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1bc
  mov 0x38(%rsp),%rdx
  lea 0x30(%rdx),%r8
  mov 0x30(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_133
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_15e
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_133:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_15e:
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rax,0x48(%rsp)
  add %rdx,%rax
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1a3
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1b2
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1a3:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1b2:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1bc:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1d7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_1f2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_20d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_224
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x74,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_210
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_10c
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x14,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_14d:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_162:
  mov %rdi,0x20(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x40(%rdx)
  movq $0x30,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ac
  mov 0x38(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ac:
  mov %rax,0x18(%rsp)
  mov %rax,0x38(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x44,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x40(%rdx)
  movq $0x30,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ed
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_202
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ed:
  mov 0x38(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_202:
  mov %rsi,0x38(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_210:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_224:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2bf
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2a1
  mov %rax,0xb8(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_88
  mov %rdx,0xa0(%rsp)
  mov %rcx,0xc8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xc8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_88:
  mov %rbx,0xa0(%rsp)
  mov %r8,0x80(%rsp)
  mov %rdi,0x78(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xb8(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_282
  mov 0x80(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x78(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_e6
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_11d
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_e6:
  mov %rbx,0x98(%rsp)
  mov 0xa0(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%r9
  mov 0x98(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_11d:
  mov %rax,0x90(%rsp)
  mov %r9,0x60(%rsp)
  mov %rcx,0x70(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb8(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x70(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_165
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_192
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_165:
  mov %rsi,0x50(%rsp)
  mov 0x90(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0xb8(%rsp),%rdx
  mov 0x50(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_192:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_264
  lea 0x60(%rbx),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_1e0
  mov %rbx,0x40(%rsp)
  mov %r8,0xa0(%rsp)
  mov %r9,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_1e0:
  mov %rcx,0x68(%rsp)
  mov %r9,0x58(%rsp)
  mov %rax,0x88(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  nop
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb8(%rsp),%rdx
  mov 0x58(%rdx),%rdx
  mov 0x68(%rsp),%rcx
  nop
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_22f
  mov 0x88(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_252
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_22f:
  mov %rdx,0x48(%rsp)
  mov 0x88(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_252:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_264:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_282:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2a1:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_2bf:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_243
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xc0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_22f
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_154
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_169:
  mov %rdi,0x20(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_1bb
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_1bb:
  mov %rax,0x18(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_1fc
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_211
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_1fc:
  mov 0x40(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_211:
  mov %rsi,0x40(%rdx)
  mov 0x38(%rsp),%rcx
  mov 0xb8(%rcx),%rcx
  mov %rcx,0x58(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_22f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_243:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_0:
  lea -0x28(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1cb
  push %rbp
  mov %rsp,%rbp
  sub $0xa0,%rsp
  mov %rbx,0xb8(%rsp)
  mov %rax,0xb0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_6c
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
  mov 0xb0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_6c:
  mov %r8,-0x8(%rdx,%rbx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x70(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x70(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_c9
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
  mov 0xb0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_c9:
  mov 0x70(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x14,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1ad
  lea 0x14(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_12c
  mov %r8,0x40(%rsp)
  mov %rdx,0x98(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x40(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_12c:
  mov %rbx,0x90(%rsp)
  mov %r9,0x60(%rsp)
  mov %rdi,0x68(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xb0(%rsp),%rdx
  mov 0x30(%rdx),%rdx
  mov 0x68(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_178
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_19b
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_178:
  mov %rdx,0x50(%rsp)
  mov 0x90(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_19b:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xa0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1ad:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_1cb:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_19e
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x2c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_18a
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  lea 0x8(%rbx),%rdx
  add $-0x8,%rdi
  lea 0x10(%rax),%rsi
  mov (%rbx),%r8
  mov %r8,0x8(%rax)
  mov %rsi,%rax
  mov %rdx,%rbx
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c7
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_68
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_68:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c1:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_c7:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  nop
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x14,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_113
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_113:
  mov %rax,0x38(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x10,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  movq $0x14,0x20(%rdx)
  movq $0x14,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_154
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_154:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_169:
  mov %rsi,0x18(%rdx)
  mov 0x68(%rsp),%rcx
  mov 0x24(%rcx),%rcx
  mov %rcx,0x30(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_18a:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_19e:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_0:
  lea -0x8(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_19f
  push %rbp
  mov %rsp,%rbp
  add $-0x80,%rsp
  mov %rbx,0x98(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_184
  mov %rax,0x90(%rsp)
  lea 0x14(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_7c
  mov %rdx,0x78(%rsp)
  mov %rcx,0xa0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x78(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_7c:
  mov %rbx,0x78(%rsp)
  mov %r8,0x60(%rsp)
  mov %rdi,0x58(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x90(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x30,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_169
  mov 0x60(%rsp),%r8
  lea 0x30(%r8),%r9
  mov 0x58(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_cd
  mov 0x78(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_f8
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_cd:
  mov %rbx,0x70(%rsp)
  mov 0x78(%rsp),%rax
  mov %r9,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%r8
  mov %rbx,%r9
  mov 0x70(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_f8:
  mov %rax,0x68(%rsp)
  mov %r9,0x48(%rsp)
  mov %rcx,0x50(%rsp)
  add %r8,%rax
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  add $0x8,%rbx
  mov 0x90(%rsp),%rdx
  mov 0x38(%rdx),%rdx
  mov 0x50(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_13a
  mov 0x68(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_15a
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_13a:
  mov %rdx,0x40(%rsp)
  mov 0x68(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_15a:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_169:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_184:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  sub $-0x80,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_19f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_191
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x4c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_17d
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_10c
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x14,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_14d:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_162:
  mov %rsi,0x20(%rdx)
  mov 0x38(%rsp),%rcx
  mov 0x44(%rcx),%rcx
  mov %rcx,0x38(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_17d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_191:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_18b
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xa0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_177
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x40,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x40,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x40,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x40,0x10(%rdx)
  movq $0x40,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x40,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_154
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_169:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_177:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_18b:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_d6
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x48(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x48(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_7b
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_7b:
  mov 0x48(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_be
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_be:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_d6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_e1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_cc
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rcx
  mov 0x48(%rsp),%rdx
  mov %rcx,0x10(%rdx)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_cc:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_206
  push %rbp
  mov %rsp,%rbp
  sub $0x30,%rsp
  mov %rbx,0x48(%rsp)
  nop
  cmp $0x6030,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_7d
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x200,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x40(%rsp),%rdx
  movq $0x200,0x10(%rdx)
  movq $0x200,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_75:
  mov %rax,0x8(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_a0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_7d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x30,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91:
  mov %r10,(%rsi,%r8,8)
  lea 0x1(%rdi),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_a0:
  cmp $0x200,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_156
  mov %rax,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  nop
  callq runtime.makeslice
  mov %rax,0x28(%rsp)
  mov 0x18(%rsp),%rdx
  lea (%rdx,%rdx,2),%rdx
  mov %rdx,0x20(%rsp)
  shl $0x4,%rdx
  mov 0x48(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  mov 0x18(%rsp),%rdi
  nop
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1ff
  mov 0x8(%rdx),%rsi
  mov 0x20(%rsp),%r8
  movq $0x30,0x8(%rsi,%r8,8)
  movq $0x30,0x10(%rsi,%r8,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_137
  mov 0x28(%rsp),%r10
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_137:
  mov (%rsi,%r8,8),%r9
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%r10
  mov %r10,(%r11)
  mov %r9,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_91
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_156:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x40(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_197:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x48(%rsp),%rbx
  add $0x6000,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1db
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1db:
  mov 0x20(%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1f1:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x30,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_1ff:
  nop
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_206:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_243
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  mov %rax,0xb8(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_88
  mov %rcx,0xc8(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xc8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xb8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_88:
  mov 0x78(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x20,0x18(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_225
  lea 0x20(%rdx),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_ec
  mov %rdx,0x30(%rsp)
  mov %r8,0xa0(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov 0xa0(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_ec:
  mov %rdi,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rbx,0x98(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xb8(%rsp),%rsi
  mov 0x28(%rsi),%rdi
  nop
  nop
  nop
  lea 0x58(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x58(%rsp)
  mov 0x40(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_14f
  mov 0x98(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_17b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_14f:
  mov 0x98(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_17b:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x30(%rsi),%rbx
  cmpq $0x60,0x38(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_207
  lea 0x60(%rdx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_1c9
  mov %rbx,0xa0(%rsp)
  mov %rdx,0x28(%rsp)
  mov %r8,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rbx,%r8
  mov 0xa0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_1c9:
  mov %rax,0xa0(%rsp)
  mov %rcx,0x50(%rsp)
  mov %r8,0x48(%rsp)
  add %rdx,%rax
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0xa0(%rsp),%rax
  mov 0x48(%rsp),%rbx
  mov 0x50(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_207:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_225:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_243:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_2b1
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x90,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_29d
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_bc
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_60
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_60:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_b6
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_b6:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_bc:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x20,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_fd:
  mov %rax,0x38(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x8,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x20,0x18(%rax)
  movq $0x20,0x20(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_13e
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_13e:
  mov 0x10(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_153:
  mov %rsi,0x10(%rax)
  mov 0x78(%rsp),%rbx
  add $0x28,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x28,%rdi
  add $0x28,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_18b
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_18b:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e1
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e1:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_1e7:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  nop
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x60,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_233:
  mov %rax,0x38(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x30,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x60,0x38(%rdx)
  movq $0x60,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_274
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_289
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_274:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_289:
  mov %rsi,0x30(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_29d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_2b1:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1c2
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  mov %rax,0x80(%rsp)
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
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_80
  mov %rcx,0x90(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x90(%rsp),%rcx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_80:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x30,0x18(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1a7
  lea 0x30(%rdx),%r9
  nop
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_dc
  mov %r8,0x68(%rsp)
  mov %rdx,0x28(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov 0x68(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_dc:
  mov %rdi,0x58(%rsp)
  mov %r9,0x50(%rsp)
  mov %rbx,0x68(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  mov 0x28(%rdx),%rbx
  cmpq $0x14,0x30(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_18c
  mov 0x50(%rsp),%rdx
  lea 0x14(%rdx),%r8
  mov 0x58(%rsp),%rcx
  nop
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_12c
  mov 0x68(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_157
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_12c:
  mov %rbx,0x60(%rsp)
  mov 0x68(%rsp),%rax
  mov %r8,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
  mov %rbx,%r8
  mov 0x60(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_157:
  mov %r8,0x58(%rsp)
  mov %rax,0x68(%rsp)
  mov %rcx,0x50(%rsp)
  add %rdx,%rax
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rax
  mov 0x58(%rsp),%rbx
  mov 0x50(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_18c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1a7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_1c2:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_21a
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x4c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_206
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_b4
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_56:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_ae:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_b4:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x18(%rdx)
  movq $0x30,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_ff
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_ff:
  mov %rax,0x38(%rsp)
  mov %rax,0x10(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  movq $0x30,0x18(%rdx)
  movq $0x30,0x20(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_142
  mov 0x38(%rsp),%rdi
  nop
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_157
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_142:
  mov 0x10(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_157:
  mov %rdi,0x10(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x30(%rdx)
  movq $0x14,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_19c
  mov 0x28(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_19c:
  mov %rax,0x38(%rsp)
  mov %rax,0x28(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x38,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  movq $0x14,0x30(%rdx)
  movq $0x14,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_1dd
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_1f2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_1dd:
  mov 0x28(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_1f2:
  mov %rsi,0x28(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_206:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_21a:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_17d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_162
  mov %rax,0x60(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_6b:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x48(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_147
  mov 0x30(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x38(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_12e
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_13d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_12e:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_13d:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_147:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_162:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_17d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_184
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x40,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_170
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_10c
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x20,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_14d:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_162:
  mov %rsi,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_170:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_184:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_101
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_e6
  mov %rax,0x78(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_74
  mov %rcx,0x88(%rsp)
  mov %rdx,0x60(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_74:
  mov %rbx,0x58(%rsp)
  mov %r8,0x48(%rsp)
  mov %rdi,0x50(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  add $0x8,%rbx
  mov 0x78(%rsp),%rdx
  mov 0x20(%rdx),%rdx
  mov 0x50(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_b7
  mov 0x58(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_d7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_b7:
  mov %rdx,0x40(%rsp)
  mov 0x58(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_d7:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_e6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_101:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_f6
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x28,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_e2
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_c7:
  mov %rsi,0x8(%rdx)
  mov 0x38(%rsp),%rcx
  mov 0x20(%rcx),%rcx
  mov %rcx,0x20(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_e2:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_f6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_0:
  lea -0x48(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2e1
  push %rbp
  mov %rsp,%rbp
  sub $0xc0,%rsp
  mov %rbx,0xd8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2c2
  mov %rax,0xd0(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_88
  mov %rcx,0xe0(%rsp)
  mov %rdx,0xb8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xe0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_88:
  mov %rdi,0x98(%rsp)
  mov %r8,0x90(%rsp)
  mov %rbx,0xb8(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xd0(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2a4
  mov 0x90(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x98(%rsp),%rcx
  nop
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_ef
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_126
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_ef:
  mov %rbx,0xb0(%rsp)
  mov 0xb8(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%r8
  mov %rbx,%r9
  mov 0xb0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_126:
  mov %rcx,0x68(%rsp)
  mov %r9,0x60(%rsp)
  mov %rax,0xa8(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0xd0(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x68(%rsp),%rcx
  nop
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_16f
  mov 0xa8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_19a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_16f:
  mov %rsi,0x48(%rsp)
  mov 0xa8(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_19a:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_286
  lea 0x60(%rbx),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_1e8
  mov %rbx,0x40(%rsp)
  mov %r8,0xb8(%rsp)
  mov %r9,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xb8(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_1e8:
  mov %r9,0x50(%rsp)
  mov %rax,0xa0(%rsp)
  mov %rcx,0x58(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xd0(%rsp),%rsi
  mov 0x58(%rsi),%rsi
  nop
  nop
  nop
  lea 0x70(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x70(%rsp)
  mov 0x58(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_249
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_26d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_249:
  mov 0xa0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x50(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_26d:
  mov 0x70(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_286:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2a4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2c2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xc0,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_2e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ce
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rbx,0x58(%rsp)
  nop
  cmp $0xc0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ba
  mov %rax,0x50(%rsp)
  mov %rdi,0x68(%rsp)
  mov %rbx,0x58(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_7d:
  mov %rax,0x28(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x58(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_ba
  mov 0x28(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_ba:
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_d1:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_116
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_116:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x58(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_157
  mov 0x28(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_171
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_157:
  mov 0x20(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_171:
  mov %rdi,0x20(%rdx)
  mov 0x58(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_1c3
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_1c3:
  mov %rax,0x28(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x58(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rax
  movq $0x60,0x48(%rax)
  movq $0x60,0x50(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_204
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_219
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_204:
  mov 0x40(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_219:
  mov %rsi,0x40(%rax)
  mov 0x58(%rsp),%rbx
  add $0xb8,%rbx
  mov 0x68(%rsp),%rdi
  add $-0xb8,%rdi
  add $0x58,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2b4
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_256
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_256:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ae:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2b4:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ba:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_2ce:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_f5
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x50(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x50(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_80
  mov %rax,0x80(%rsp)
  mov %rcx,0x90(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x90(%rsp),%rcx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_80:
  mov 0x50(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x30(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x30(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_d9
  mov %rdx,0x28(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_d9:
  mov 0x30(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_f5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_167
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_153
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  mov %rdi,0x70(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_b9
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_5a
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_5a:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+34162(%rip),%rax
  mov $0xf,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xf,0x8(%rax)
  lea go_string._+34162(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_b3:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_b9:
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0x70(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x58(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  nop
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_f1
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_f1:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+34177(%rip),%rax
  mov $0xf,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_147
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xf,0x8(%rax)
  lea go_string._+34177(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_147:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_14d:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_153:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_167:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_147
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov %rax,0xa0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x70(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x70(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_88
  mov %rcx,0xb0(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_88:
  mov 0x70(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_d3
  mov %r8,0x48(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_d3:
  mov %r8,-0x8(%rdx,%rbx,1)
  lea 0x8(%rdx),%r8
  mov 0x18(%rax),%r9
  nop
  nop
  nop
  lea 0x50(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x50(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_128
  mov %rdx,0x40(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_128:
  mov 0x50(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_147:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_173
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x18,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_15f
  mov %rax,0x58(%rsp)
  mov %rdi,0x70(%rsp)
  mov %rbx,0x60(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_5a
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_5a:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+18141(%rip),%rax
  mov $0x9,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18141(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b3:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_b9:
  mov 0x60(%rsp),%rbx
  lea 0x10(%rbx),%rdx
  mov 0x70(%rsp),%rdi
  add $-0x10,%rdi
  mov 0x58(%rsp),%rax
  lea 0x18(%rax),%rsi
  mov 0x8(%rbx),%r8
  mov %r8,0x10(%rax)
  mov %rsi,%rax
  mov %rdx,%rbx
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_fd
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_fd:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+52923(%rip),%rax
  mov $0x15,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_153
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+52923(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_153:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_159:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_15f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_173:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_372
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  cmp $0x24,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2f9
  mov 0x20(%rbx),%edx
  nop
  nop
  cmp $0x24,%rdx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2e2
  mov %rax,0x98(%rsp)
  mov %rdi,0xb0(%rsp)
  mov %rcx,0xa8(%rsp)
  mov %rbx,0xa0(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x98(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  mov 0xb0(%rsp),%rsi
  add $-0x24,%rsi
  mov %rsi,0x28(%rsp)
  neg %rsi
  sar $0x3f,%rsi
  and $0x24,%esi
  mov 0xa0(%rsp),%rbx
  add %rbx,%rsi
  mov %rsi,0x38(%rsp)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_cc
  mov 0x8(%rdx),%r8
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %r8,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_cc:
  mov %rax,0x40(%rsp)
  mov %rax,0x8(%rdx)
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x98(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_109
  mov 0x40(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_109:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x40(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_11e:
  mov %rdi,0x8(%rdx)
  mov 0xa8(%rsp),%rcx
  add $-0x24,%rcx
  test $0x7,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_242
  shr $0x3,%rcx
  nop
  cmp $0x80,%rcx
  jg L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1a5
  mov %rcx,0x30(%rsp)
  lea type__+387456(%rip),%rax
  mov %rcx,%rbx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  mov 0x98(%rsp),%rsi
  mov %rdx,0x28(%rsi)
  mov %rdx,0x30(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_18c
  mov 0x20(%rsi),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_18c:
  mov %rax,0x20(%rsi)
  mov 0x28(%rsp),%rcx
  mov 0x38(%rsp),%rdi
  xor %eax,%eax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_320
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1a5:
  lea 0x48(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x48(%rsp)
  mov %rax,0x50(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1dc
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_1dc:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0x58(%rsp)
  mov %rdx,0x60(%rsp)
  lea go_string._+151877(%rip),%rax
  mov $0x3f,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_239
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x3f,0x8(%rax)
  lea go_string._+151877(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_239:
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_242:
  lea 0x68(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x68(%rsp)
  mov %rax,0x70(%rsp)
  mov ssz.ErrIncorrectListSize(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_279
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_279:
  mov ssz.ErrIncorrectListSize+8(%rip),%rdx
  mov %rcx,0x78(%rsp)
  mov %rdx,0x80(%rsp)
  lea go_string._+164572(%rip),%rax
  mov $0x4a,%ebx
  lea 0x68(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2d9
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x4a,0x8(%rax)
  lea go_string._+164572(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2d9:
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2e2:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_2f9:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_310:
  mov 0x20(%rsi),%r8
  mov %r11,(%r8,%r10,8)
  mov %r9,%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_320:
  cmp %rdx,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_355
  lea 0x1(%rax),%r8
  mov %r8,%r9
  shl $0x3,%r8
  cmp %rcx,%r8
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_36c
  mov %rax,%r10
  shl $0x3,%rax
  nop
  cmp %rax,%r8
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_367
  mov 0x28(%rsi),%r8
  nop
  mov (%rdi,%r10,8),%r11
  cmp %r8,%r10
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_310
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_362
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_355:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_362:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_367:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_36c:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_372:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_0:
  lea -0x60(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_321
  push %rbp
  mov %rsp,%rbp
  sub $0xd8,%rsp
  mov %rbx,0xf0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_302
  mov %rax,0xe8(%rsp)
  lea 0x4(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_90
  mov %rcx,0xf8(%rsp)
  mov %rdx,0xd0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xe8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_90:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x20,0x28(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2e4
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_ec
  mov %rdx,0xd0(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xd0(%rsp),%rdx
  mov 0x58(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_ec:
  mov %rdi,0x50(%rsp)
  mov %r9,0x40(%rsp)
  mov %rbx,0xc8(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x40(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe8(%rsp),%rsi
  mov 0x38(%rsi),%rdi
  nop
  nop
  nop
  lea 0xa0(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0xa0(%rsp)
  mov 0x50(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_154
  mov 0xc8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_180
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_154:
  mov 0xc8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_180:
  mov 0xa0(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x40(%rsi),%rbx
  cmpq $0x20,0x48(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2c6
  lea 0x20(%rdx),%r8
  nop
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_1d6
  mov %rdx,0x30(%rsp)
  mov %rbx,0xd0(%rsp)
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0xd0(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_1d6:
  mov %rcx,0x48(%rsp)
  mov %r8,0x38(%rsp)
  mov %rax,0xc0(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe8(%rsp),%rsi
  mov 0x58(%rsi),%rdi
  nop
  nop
  nop
  lea 0x80(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x80(%rsp)
  mov 0x48(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_23a
  mov 0xc0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_266
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_23a:
  mov 0xc0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe8(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_266:
  mov 0x80(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x60(%rsi),%r8
  nop
  nop
  nop
  lea 0x60(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x60(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2b0
  mov %rdx,0x28(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2b0:
  mov 0x60(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2c6:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_2e4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_302:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd8,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_321:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ce
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x5c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ba
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_7d:
  mov %rax,0x8(%rdx)
  mov 0x78(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_b3
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_b3:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_f8
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_f8:
  mov %rax,0x58(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x4,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x20,0x28(%rax)
  movq $0x20,0x30(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_139
  mov 0x58(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_151
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_139:
  mov 0x20(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_151:
  mov %rsi,0x20(%rax)
  mov 0x78(%rsp),%rbx
  add $0x24,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x24,%rdi
  add $0x38,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_1e7
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_189
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_189:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+43515(%rip),%rax
  mov $0x12,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_1e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43515(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_1e1:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_1e7:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x20,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_22c
  mov 0x40(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_22c:
  mov %rax,0x58(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x2c,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x20,0x48(%rax)
  movq $0x20,0x50(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_26d
  mov 0x58(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_282
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_26d:
  mov 0x40(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_282:
  mov %rsi,0x40(%rax)
  mov 0x78(%rsp),%rbx
  add $0x4c,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x4c,%rdi
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_319
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_2ba
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_2ba:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+26459(%rip),%rax
  mov $0xc,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_313
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xc,0x8(%rax)
  lea go_string._+26459(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_313:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_319:
  mov 0x78(%rsp),%rbx
  add $0x54,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x54,%rdi
  mov 0x70(%rsp),%rax
  add $0x60,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_356
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_356:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+64155(%rip),%rax
  mov $0x19,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x19,0x8(%rax)
  lea go_string._+64155(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ae:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3b4:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ba:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_3ce:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_0:
  lea -0x58(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_319
  push %rbp
  mov %rsp,%rbp
  sub $0xd0,%rsp
  mov %rbx,0xe8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2fb
  mov %rax,0xe0(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_88
  mov %rcx,0xf0(%rsp)
  mov %rdx,0xc8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_88:
  mov %rdi,0x50(%rsp)
  mov %r8,0x48(%rsp)
  mov %rbx,0xc8(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0xe0(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  cmpq $0x1,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2dd
  mov 0x48(%rsp),%rbx
  lea 0x1(%rbx),%r8
  mov 0x50(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_e3
  mov 0xc8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_11f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_e3:
  mov %rsi,0xc0(%rsp)
  mov 0xc8(%rsp),%rax
  mov %r8,%rbx
  mov $0x1,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rdx
  mov 0xc0(%rsp),%rsi
  mov %rbx,%r8
  mov 0x48(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_11f:
  movzbl (%rsi),%r9d
  mov %r9b,(%rax,%rbx,1)
  mov 0x38(%rdx),%rbx
  cmpq $0x14,0x40(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2bf
  lea 0x14(%r8),%r9
  cmp %r9,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_175
  mov %rbx,0xc8(%rsp)
  mov %r8,0x50(%rsp)
  mov %r9,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x50(%rsp),%r8
  mov %rbx,%r9
  mov 0xc8(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_175:
  mov %rcx,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rax,0xb8(%rsp)
  add %r8,%rax
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe0(%rsp),%rsi
  mov 0x50(%rsi),%rdi
  nop
  nop
  nop
  lea 0x98(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x98(%rsp)
  mov 0x40(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_1d9
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_205
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_1d9:
  mov 0xb8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_205:
  mov 0x98(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x58(%rsi),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_257
  mov %rdx,0x30(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov 0xe0(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_257:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  lea 0x8(%rbx),%rdx
  mov 0x60(%rsi),%r8
  nop
  nop
  nop
  lea 0x58(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x58(%rsp)
  nop
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2a6
  mov %rbx,0x28(%rsp)
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x28(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2a6:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2bf:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2dd:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_2fb:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_319:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3c7
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x5d,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3b3
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_7d:
  mov %rax,0x58(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x78(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_ba
  mov 0x58(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_ba:
  mov 0x8(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_d1:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x1,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x1,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_116
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_116:
  mov %rax,0x20(%rdx)
  mov 0x78(%rsp),%rsi
  movzbl 0x30(%rsi),%edi
  mov %dil,(%rax)
  movq $0x1,0x28(%rdx)
  movq $0x1,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_14f
  mov 0x20(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_14f:
  mov %rax,0x20(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x40(%rdx)
  movq $0x14,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_194
  mov 0x38(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_194:
  mov %rax,0x58(%rsp)
  mov %rax,0x38(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x31,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x14,0x40(%rax)
  movq $0x14,0x48(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1d5
  mov 0x58(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1ea
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1d5:
  mov 0x38(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x58(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_1ea:
  mov %rsi,0x38(%rax)
  mov 0x78(%rsp),%rbx
  add $0x45,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x45,%rdi
  add $0x50,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Gwei.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_27e
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_222
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_222:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+23990(%rip),%rax
  mov $0xb,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_278
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xb,0x8(%rax)
  lea go_string._+23990(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_278:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_27e:
  mov 0x78(%rsp),%rbx
  add $0x4d,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x4d,%rdi
  mov 0x70(%rsp),%rax
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_314
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_2b7
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_2b7:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+37050(%rip),%rax
  mov $0x10,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_30e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x10,0x8(%rax)
  lea go_string._+37050(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_30e:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_314:
  mov 0x78(%rsp),%rbx
  add $0x55,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x55,%rdi
  mov 0x70(%rsp),%rax
  add $0x60,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  nop
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3ad
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_351
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_351:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+52923(%rip),%rax
  mov $0x15,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3a7
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+52923(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3a7:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3ad:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3b3:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_3c7:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Builder.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_196
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_178
  mov %rax,0xa0(%rsp)
  lea 0x14(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_88
  mov %rcx,0xb0(%rsp)
  mov %rdx,0x88(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x88(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_88:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x80(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xa0(%rsp),%rsi
  mov 0x20(%rsi),%rdi
  nop
  nop
  nop
  lea 0x60(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x60(%rsp)
  mov 0x38(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_ef
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_11b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_ef:
  mov 0x80(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_11b:
  mov 0x60(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x28(%rsi),%r8
  nop
  nop
  nop
  lea 0x40(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x40(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_162
  mov %rdx,0x28(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_162:
  mov 0x40(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_178:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_196:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_213
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x24,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1ff
  mov %rax,0x60(%rsp)
  mov %rdi,0x78(%rsp)
  mov %rbx,0x68(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_7a:
  mov %rax,0x28(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x68(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x14,0x10(%rax)
  movq $0x14,0x18(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_b7
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_b7:
  mov 0x8(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rax)
  mov 0x68(%rsp),%rbx
  add $0x14,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x14,%rdi
  add $0x20,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Gwei.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_167
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_106
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_106:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+21296(%rip),%rax
  mov $0xa,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xa,0x8(%rax)
  lea go_string._+21296(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_161:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_167:
  mov 0x68(%rsp),%rbx
  add $0x1c,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x1c,%rdi
  mov 0x60(%rsp),%rax
  add $0x28,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.BuilderIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1f9
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_19d
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_19d:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+37034(%rip),%rax
  mov $0x10,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1f3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x10,0x8(%rax)
  lea go_string._+37034(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1f3:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1f9:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_1ff:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_213:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPendingWithdrawal.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_7f
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x28(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x28(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_63
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_63:
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_7f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderPreferences.MarshalSSZTo_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_11f
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_104
  mov %rax,0x78(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_74
  mov %rcx,0x88(%rsp)
  mov %rdx,0x60(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x60(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x88(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_74:
  mov %rbx,0x58(%rsp)
  mov %rdi,0x30(%rsp)
  mov %r8,0x28(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x28(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0x78(%rsp),%rsi
  mov 0x20(%rsi),%rsi
  nop
  nop
  nop
  lea 0x38(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x38(%rsp)
  mov 0x30(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_cd
  mov 0x58(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_ee
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_cd:
  mov 0x58(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x28(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_ee:
  mov 0x38(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_104:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_11f:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_181
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rbx,0x58(%rsp)
  nop
  cmp $0x28,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_16d
  mov %rax,0x50(%rsp)
  mov %rdi,0x68(%rsp)
  mov %rbx,0x58(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_7a:
  mov %rax,0x28(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x58(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rax
  movq $0x20,0x10(%rax)
  movq $0x20,0x18(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_b7
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_b7:
  mov 0x8(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rax)
  mov 0x58(%rsp),%rbx
  add $0x20,%rbx
  mov 0x68(%rsp),%rdi
  add $-0x20,%rdi
  add $0x20,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_167
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_106
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_106:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_161:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_167:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_16d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_181:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnGroupID.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1e2
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rbx,0x58(%rsp)
  nop
  cmp $0x2a,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1ce
  mov %rax,0x50(%rsp)
  mov %rdi,0x68(%rsp)
  mov %rbx,0x58(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x50(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_7a:
  mov %rax,0x28(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x58(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rax
  movq $0x20,0x10(%rax)
  movq $0x20,0x18(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_b7
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_b7:
  mov 0x8(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rax)
  mov 0x58(%rsp),%rbx
  add $0x20,%rbx
  mov 0x68(%rsp),%rdi
  add $-0x20,%rdi
  add $0x20,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_167
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_106
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_106:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_161:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_167:
  mov 0x58(%rsp),%rcx
  movzbl 0x28(%rcx),%edx
  cmp $0x1,%dl
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1ba
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_182
  mov 0x50(%rsp),%rdx
  movb $0x1,0x28(%rdx)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_18b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_182:
  mov 0x50(%rsp),%rdx
  movb $0x0,0x28(%rdx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_18b:
  movzbl 0x29(%rcx),%ecx
  cmp $0x1,%cl
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1a6
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_19c
  movb $0x1,0x29(%rdx)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1a0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_19c:
  movb $0x0,0x29(%rdx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1a0:
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1a6:
  mov ssz.ErrInvalidSerialization(%rip),%rax
  mov ssz.ErrInvalidSerialization+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1ba:
  mov ssz.ErrInvalidSerialization(%rip),%rax
  mov ssz.ErrInvalidSerialization+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1ce:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_1e2:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PayloadAttestationData.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_0:
  lea -0x58(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_281
  push %rbp
  mov %rsp,%rbp
  sub $0xd0,%rsp
  mov %rbx,0xe8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x20,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_262
  mov %rax,0xe0(%rsp)
  lea 0x20(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_88
  mov %rdx,0xc8(%rsp)
  mov %rcx,0xf0(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xf0(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_88:
  mov %rdi,0x60(%rsp)
  mov %r8,0x58(%rsp)
  mov %rbx,0xb8(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xe0(%rsp),%rsi
  mov 0x20(%rsi),%rdi
  nop
  nop
  nop
  lea 0x98(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x98(%rsp)
  mov 0x60(%rsp),%rcx
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_f0
  mov 0xb8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_11c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_f0:
  mov 0xb8(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xe0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x58(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_11c:
  mov 0x98(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  lea 0x8(%rdx),%rbx
  mov 0x28(%rsi),%r8
  nop
  nop
  nop
  lea 0x78(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x78(%rsp)
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_172
  mov %rdx,0x48(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov 0xe0(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_172:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rdx,1)
  mov 0x30(%rsi),%rdx
  cmpq $0x14,0x38(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_244
  lea 0x14(%rbx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_1c4
  mov %rbx,0x40(%rsp)
  mov %rdx,0xc8(%rsp)
  mov %r8,%rbx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc8(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_1c4:
  mov %r8,0x68(%rsp)
  mov %rax,0xc0(%rsp)
  mov %rcx,0x70(%rsp)
  add %rbx,%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rbx
  add $0x8,%rbx
  mov 0xe0(%rsp),%rdx
  mov 0x48(%rdx),%rdx
  mov 0x70(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_20f
  mov 0xc0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_232
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_20f:
  mov %rdx,0x50(%rsp)
  mov 0xc0(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x50(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_232:
  mov %rdx,-0x8(%rbx,%rax,1)
  xor %edi,%edi
  xor %esi,%esi
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_244:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_262:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xd0,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_281:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2d7
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x4c,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2c3
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_7d:
  mov %rax,0x38(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x78(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rax
  movq $0x20,0x10(%rax)
  movq $0x20,0x18(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_ba
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_ba:
  mov 0x8(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_d1:
  mov %rsi,0x8(%rax)
  mov 0x78(%rsp),%rbx
  add $0x20,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x20,%rdi
  add $0x20,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_167
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_109
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_109:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+37066(%rip),%rax
  mov $0x10,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x10,0x8(%rax)
  lea go_string._+37066(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_161:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_167:
  mov 0x78(%rsp),%rbx
  add $0x28,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x28,%rdi
  mov 0x70(%rsp),%rax
  add $0x28,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1fc
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1a0
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1a0:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1f6
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1f6:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_1fc:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x14,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_24c
  mov 0x30(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_24c:
  mov %rax,0x38(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x30,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x14,0x38(%rdx)
  movq $0x14,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_28d
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2a2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_28d:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2a2:
  mov %rsi,0x30(%rdx)
  mov 0x78(%rsp),%rcx
  mov 0x44(%rcx),%rcx
  mov %rcx,0x48(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2c3:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_2d7:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerPreferences.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_122
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  mov %rax,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x50(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x50(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_80
  mov %rcx,0x90(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x90(%rsp),%rcx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_80:
  mov 0x50(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_cb
  mov %r8,0x48(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_cb:
  mov %r8,-0x8(%rdx,%rbx,1)
  add $0x8,%rdx
  mov 0x18(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_10a
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_10a:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_122:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_e8
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x18,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_d4
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+29259(%rip),%rax
  mov $0xd,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29259(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  mov 0x48(%rsp),%rsi
  mov %rdx,0x10(%rsi)
  mov 0x10(%rcx),%rcx
  mov %rcx,0x18(%rsi)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_d4:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_e8:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlocksByRangeRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_d6
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x48(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x48(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_7b
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_7b:
  mov 0x48(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_be
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_be:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_d6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_e1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_cc
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+29259(%rip),%rax
  mov $0xd,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29259(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rcx
  mov 0x48(%rsp),%rdx
  mov %rcx,0x10(%rdx)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_cc:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecarsByRangeRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_d6
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x48(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x48(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_7b
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_7b:
  mov 0x48(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_be
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_be:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_d6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_e1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_cc
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+29259(%rip),%rax
  mov $0xd,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29259(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rcx
  mov 0x48(%rsp),%rdx
  mov %rcx,0x10(%rdx)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_cc:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ExecutionPayloadEnvelopesByRangeRequest.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1f3
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x14,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1d5
  mov %rax,0x98(%rsp)
  lea 0x14(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_88
  mov %rdx,0x80(%rsp)
  mov %rcx,0xa8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x14,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_88:
  mov %rbx,0x78(%rsp)
  mov %r8,0x58(%rsp)
  mov %rdi,0x60(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x58(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  mov 0x60(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_ce
  mov 0x78(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_f6
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_ce:
  mov %rsi,0x50(%rsp)
  mov 0x78(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x50(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_f6:
  mov %rsi,-0x8(%rbx,%rax,1)
  add $0x8,%rbx
  mov 0x28(%rdx),%r8
  cmp %rbx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_12b
  mov %r8,0x48(%rsp)
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x48(%rsp),%r8
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_12b:
  mov %r8,-0x8(%rbx,%rax,1)
  mov 0x30(%rdx),%r8
  cmpq $0x30,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1b7
  lea 0x30(%rbx),%rdx
  nop
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_176
  mov %rbx,0x40(%rsp)
  mov %r8,0x80(%rsp)
  mov %rdx,%rbx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_176:
  mov %rdx,0x70(%rsp)
  mov %rcx,0x68(%rsp)
  mov %rax,0x80(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  mov 0x70(%rsp),%rbx
  mov 0x68(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1b7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1d5:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_1f3:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_199
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x54,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_185
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x14(%rsi),%rdi
  mov %rdi,0x20(%rdx)
  mov 0x1c(%rsi),%rsi
  mov %rsi,0x28(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x30,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_121
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_121:
  mov %rax,0x18(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x24,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x38(%rdx)
  movq $0x30,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_162
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_177
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_162:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_177:
  mov %rsi,0x30(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_185:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_199:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorRegistrationV1.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_0:
  lea -0x18(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_1aa
  push %rbp
  mov %rsp,%rbp
  sub $0x90,%rsp
  mov %rbx,0xa8(%rsp)
  mov %rax,0xa0(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x60(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x60(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_88
  mov %rcx,0xb0(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xb0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_88:
  mov 0x60(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  mov 0x10(%rax),%r8
  cmpq $0x30,0x18(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_18c
  lea 0x30(%rdx),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_ec
  mov %rdx,0x28(%rsp)
  mov %r8,0x88(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov 0x88(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_ec:
  mov %rbx,0x80(%rsp)
  mov %r9,0x30(%rsp)
  mov %rdi,0x38(%rsp)
  lea (%rbx,%rdx,1),%rax
  mov %r8,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xa0(%rsp),%rsi
  mov 0x28(%rsi),%rsi
  nop
  nop
  nop
  lea 0x40(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x40(%rsp)
  mov 0x38(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_14f
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_173
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_14f:
  mov 0x80(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_173:
  mov 0x40(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_18c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x90,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_1aa:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorIdentity.MarshalSSZTo_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_0:
  lea -0x20(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2ff
  push %rbp
  mov %rsp,%rbp
  sub $0x98,%rsp
  mov %rbx,0xb0(%rsp)
  mov %rax,0xa8(%rsp)
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
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_88
  mov %rcx,0xb8(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0xb8(%rsp),%rcx
  mov %rax,%rbx
  mov 0xa8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_88:
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
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_e9
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
  mov 0xa8(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_e9:
  mov 0x48(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov 0x18(%rax),%rdx
  cmpq $0x20,0x20(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2e1
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_14c
  mov %rdx,0x90(%rsp)
  mov %r8,0x28(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x90(%rsp),%rdx
  mov 0x28(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_14c:
  mov %rbx,0x90(%rsp)
  mov %r9,0x40(%rsp)
  mov %rdi,0x38(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xa8(%rsp),%rdx
  mov 0x30(%rdx),%rbx
  cmpq $0x20,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2c2
  mov 0x40(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x38(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1a3
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1d7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1a3:
  mov %rbx,0x88(%rsp)
  mov 0x90(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%r9
  mov 0x88(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_1d7:
  mov %rcx,0x40(%rsp)
  mov %r9,0x38(%rsp)
  mov %rax,0x90(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0xa8(%rsp),%rdx
  mov 0x48(%rdx),%rbx
  cmpq $0x20,0x50(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2a4
  mov 0x38(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x40(%rsp),%rcx
  nop
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_22f
  mov 0x90(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_263
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_22f:
  mov %rbx,0x88(%rsp)
  mov 0x90(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%rdx
  mov %rbx,%r8
  mov 0x88(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_263:
  mov %rcx,0x40(%rsp)
  mov %r8,0x38(%rsp)
  mov %rax,0x90(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x90(%rsp),%rax
  mov 0x38(%rsp),%rbx
  mov 0x40(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2a4:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2c2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2e1:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x98,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_2ff:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_359
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  nop
  cmp $0x70,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_345
  mov %rax,0x70(%rsp)
  mov %rdi,0x88(%rsp)
  mov %rbx,0x78(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_5d
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_5d:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+14986(%rip),%rax
  mov $0x8,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+14986(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b3:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_b9:
  mov 0x78(%rsp),%rbx
  add $0x8,%rbx
  mov 0x88(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x70(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_f6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_f6:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+40193(%rip),%rax
  mov $0x11,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_14e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x11,0x8(%rax)
  lea go_string._+40193(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_14e:
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_154:
  mov %rbx,0x30(%rsp)
  mov %rax,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_19f
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_19f:
  mov %rax,0x38(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x10,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1e2
  mov 0x38(%rsp),%rdi
  nop
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1f7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1e2:
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_1f7:
  mov %rdi,0x18(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_23c
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_23c:
  mov %rax,0x38(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_27d
  mov 0x38(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_292
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_27d:
  mov 0x30(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_292:
  mov %rdi,0x30(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x70(%rsp),%rdx
  movq $0x0,0x50(%rdx)
  movq $0x20,0x58(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_2d7
  mov 0x48(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_2d7:
  mov %rax,0x38(%rsp)
  mov %rax,0x48(%rdx)
  mov 0x78(%rsp),%rbx
  add $0x50,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x70(%rsp),%rdx
  movq $0x20,0x50(%rdx)
  movq $0x20,0x58(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_318
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_331
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_318:
  mov 0x48(%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_331:
  mov %rsi,0x48(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_345:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_359:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_246
  push %rbp
  mov %rsp,%rbp
  sub $0x58,%rsp
  mov %rbx,0x70(%rsp)
  nop
  cmp $0x4d8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_85
  mov %rax,0x68(%rsp)
  mov %rdi,0x80(%rsp)
  mov %rbx,0x70(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x21,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x68(%rsp),%rdx
  movq $0x21,0x10(%rdx)
  movq $0x21,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_7d
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_7d:
  mov %rax,0x8(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_a2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_85:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99:
  mov %r9,(%rdi,%rsi,8)
  mov 0x28(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_a2:
  cmp $0x21,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_166
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23f
  mov %rsi,0x38(%rsp)
  mov %rax,0x30(%rsp)
  mov %r8,0x28(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x40(%rsp)
  mov 0x30(%rsp),%rdx
  mov 0x70(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x68(%rsp),%rdx
  mov 0x10(%rdx),%rsi
  mov 0x38(%rsp),%rdi
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23a
  lea (%rdi,%rdi,2),%rsi
  mov 0x8(%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_14c
  mov 0x40(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_14c:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x40(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_99
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_166:
  lea type__+1421952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_182
  mov 0x68(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_197
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_182:
  mov 0x68(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_197:
  mov %rax,0x20(%rdx)
  mov 0x70(%rsp),%rbx
  add $0x420,%rbx
  mov 0x80(%rsp),%rdi
  add $-0x420,%rdi
  mov $0xb8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_234
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_1d6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_1d6:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+15010(%rip),%rax
  mov $0x8,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_22e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+15010(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_22e:
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_234:
  add $0x58,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23a:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_23f:
  nop
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_246:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_0:
  lea -0x10(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_261
  push %rbp
  mov %rsp,%rbp
  sub $0x88,%rsp
  mov %rbx,0xa0(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x30,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_243
  mov %rax,0x98(%rsp)
  lea 0x30(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_88
  mov %rcx,0xa8(%rsp)
  mov %rdx,0x80(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x30,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xa8(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_88:
  mov %rbx,0x80(%rsp)
  mov %r8,0x68(%rsp)
  mov %rdi,0x60(%rsp)
  lea (%rcx,%rbx,1),%rax
  mov %rdx,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x98(%rsp),%rdx
  mov 0x20(%rdx),%rbx
  cmpq $0x20,0x28(%rdx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_225
  mov 0x68(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x60(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_e3
  mov 0x80(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_112
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_e3:
  mov %rbx,0x78(%rsp)
  mov 0x80(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  nop
  callq runtime.growslice
  mov 0x68(%rsp),%r8
  mov %rbx,%r9
  mov 0x78(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_112:
  mov %rax,0x70(%rsp)
  mov %r9,0x50(%rsp)
  mov %rcx,0x58(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x50(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdx
  mov 0x38(%rdx),%rsi
  mov 0x58(%rsp),%rcx
  cmp %rbx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_154
  mov 0x70(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_17c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_154:
  mov %rsi,0x48(%rsp)
  mov 0x70(%rsp),%rax
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x98(%rsp),%rdx
  mov 0x48(%rsp),%rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_17c:
  mov %rsi,-0x8(%rbx,%rax,1)
  mov 0x40(%rdx),%r8
  cmpq $0x60,0x48(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_207
  lea 0x60(%rbx),%rdx
  cmp %rdx,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_1c6
  mov %r8,0x80(%rsp)
  mov %rbx,0x40(%rsp)
  mov %rdx,%rbx
  mov $0x60,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x80(%rsp),%r8
  mov %rbx,%rdx
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_1c6:
  mov %rax,0x80(%rsp)
  mov %rdx,0x68(%rsp)
  mov %rcx,0x60(%rsp)
  add %rbx,%rax
  mov %r8,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  mov 0x68(%rsp),%rbx
  mov 0x60(%rsp),%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_207:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_225:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_243:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x88,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_261:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_233
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xb8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_21f
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_169:
  mov %rdi,0x20(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_1bb
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_1bb:
  mov %rax,0x18(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_1fc
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_211
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_1fc:
  mov 0x40(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_211:
  mov %rsi,0x40(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_21f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_233:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_191
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x58,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_17d
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x30,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_74:
  mov %rax,0x18(%rsp)
  mov %rax,(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x8(%rdx)
  movq $0x30,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_b0
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_c4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_b0:
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_c4:
  mov %rdi,(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_10c
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_14d:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_162:
  mov %rsi,0x18(%rdx)
  mov 0x38(%rsp),%rcx
  mov 0x50(%rcx),%rcx
  mov %rcx,0x30(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_17d:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_191:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_177
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_15c
  mov %rax,0x70(%rsp)
  lea 0x4(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_76
  mov %rcx,0x80(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x80(%rsp),%rcx
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_76:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x4,0x28(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_141
  lea 0x4(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_cf
  mov %r8,0x50(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov 0x50(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_cf:
  mov (%rdx),%edx
  mov %edx,(%rbx,%r8,1)
  lea 0x8(%r9),%rdx
  mov 0x38(%rax),%r8
  nop
  nop
  nop
  lea 0x30(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r8,0x30(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_125
  mov %r9,0x28(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%r9
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_125:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%r9,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_141:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_15c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_177:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1d5
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1c1
  mov %rax,0x48(%rsp)
  mov %rdi,0x60(%rsp)
  mov %rbx,0x50(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_7a:
  mov %rax,0x8(%rdx)
  mov 0x50(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_b2
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_b2:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_f7
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_f7:
  mov %rax,0x20(%rdx)
  mov 0x50(%rsp),%rbx
  mov 0x4(%rbx),%esi
  mov %esi,(%rax)
  movq $0x4,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_12e
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_12e:
  mov %rax,0x20(%rdx)
  add $0x8,%rbx
  mov 0x60(%rsp),%rdi
  add $-0x8,%rdi
  lea 0x38(%rdx),%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1ba
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_15e
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_15e:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+40312(%rip),%rax
  mov $0x11,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1b4
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x11,0x8(%rax)
  lea go_string._+40312(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1b4:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1ba:
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1c1:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_1d5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_193
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x48,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_17f
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x10(%rdx)
  movq $0x20,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x20(%rsi),%rsi
  mov %rsi,0x20(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x30(%rdx)
  movq $0x20,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_119
  mov 0x28(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_119:
  mov %rax,0x18(%rsp)
  mov %rax,0x28(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x28,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x30(%rdx)
  movq $0x20,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_15a
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_171
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_15a:
  mov 0x28(%rdx),%rcx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_171:
  mov %rsi,0x28(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_17f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_193:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_177
  push %rbp
  mov %rsp,%rbp
  sub $0x60,%rsp
  mov %rbx,0x78(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_15c
  mov %rax,0x70(%rsp)
  lea 0x4(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_76
  mov %rcx,0x80(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x80(%rsp),%rcx
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_76:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x4,0x28(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_141
  lea 0x4(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_cf
  mov %r8,0x50(%rsp)
  mov %rdx,0x58(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x58(%rsp),%rdx
  mov 0x50(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
  mov 0x70(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_cf:
  mov (%rdx),%edx
  mov %edx,(%rbx,%r8,1)
  lea 0x8(%r9),%rdx
  mov 0x38(%rax),%r8
  nop
  nop
  nop
  lea 0x30(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r8,0x30(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_125
  mov %r9,0x28(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%r9
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_125:
  mov 0x30(%rsp),%r8
  mov %r8,(%rbx,%r9,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_141:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_15c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x60,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_177:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1d5
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1c1
  mov %rax,0x48(%rsp)
  mov %rdi,0x60(%rsp)
  mov %rbx,0x50(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_7a:
  mov %rax,0x8(%rdx)
  mov 0x50(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_b2
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_b2:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_f7
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_f7:
  mov %rax,0x20(%rdx)
  mov 0x50(%rsp),%rbx
  mov 0x4(%rbx),%esi
  mov %esi,(%rax)
  movq $0x4,0x28(%rdx)
  movq $0x4,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_12e
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_12e:
  mov %rax,0x20(%rdx)
  add $0x8,%rbx
  mov 0x60(%rsp),%rdi
  add $-0x8,%rdi
  lea 0x38(%rdx),%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1ba
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_15e
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_15e:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+18159(%rip),%rax
  mov $0x9,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1b4
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18159(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1b4:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1ba:
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1c1:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_1d5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_16b
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x24,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_157
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x4,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_74:
  mov %rax,(%rdx)
  mov 0x38(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x8(%rdx)
  movq $0x4,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_ac
  mov (%rdx),%rdi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_ac:
  mov %rax,(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_f3
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_f3:
  mov %rax,0x18(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x4,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_134
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_149
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_134:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_149:
  mov %rsi,0x18(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_157:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_16b:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2b0
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x80000,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_7b
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea type__+337600(%rip),%rax
  mov $0x2000,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x2000,0x8(%rdx)
  movq $0x2000,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_74:
  mov %rax,(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_a0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_7b:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f:
  mov %r9,(%rdi,%rsi,8)
  mov 0x18(%rsp),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_a0:
  cmp $0x2000,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_166
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2aa
  mov %rsi,0x28(%rsp)
  mov %rax,0x20(%rsp)
  mov %r8,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x30(%rsp)
  mov 0x20(%rsp),%rdx
  mov 0x50(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rdx
  mov 0x8(%rdx),%rsi
  mov 0x28(%rsp),%rdi
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2a5
  lea (%rdi,%rdi,2),%rsi
  mov (%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_14c
  mov 0x30(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_14c:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x30(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_8f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_166:
  lea type__+337600(%rip),%rax
  mov $0x2000,%ebx
  mov %rbx,%rcx
  callq runtime.makeslice
  mov 0x48(%rsp),%rdx
  movq $0x2000,0x20(%rdx)
  movq $0x2000,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1ac
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1ac:
  mov %rax,0x18(%rdx)
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1c0
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4:
  mov %r9,(%rdi,%rsi,8)
  mov 0x18(%rsp),%rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1c0:
  cmp $0x2000,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_28c
  mov %rax,%rsi
  shl $0x5,%rax
  lea 0x1(%rsi),%rdi
  mov %rdi,%r8
  shl $0x5,%rdi
  nop
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_29b
  mov %rsi,0x28(%rsp)
  mov %rax,0x20(%rsp)
  mov %r8,0x18(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov %rax,0x30(%rsp)
  mov 0x20(%rsp),%rdx
  mov 0x50(%rsp),%rsi
  lea (%rsi,%rdx,1),%rbx
  lea 0x40000(%rbx),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  mov 0x28(%rsp),%rdi
  nop
  cmp %rsi,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_296
  lea (%rdi,%rdi,2),%rsi
  mov 0x18(%rdx),%rdi
  movq $0x20,0x8(%rdi,%rsi,8)
  movq $0x20,0x10(%rdi,%rsi,8)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_272
  mov 0x30(%rsp),%r9
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_272:
  mov (%rdi,%rsi,8),%r8
  callq runtime.gcWriteBarrier2
  mov 0x30(%rsp),%r9
  mov %r9,(%r11)
  mov %r8,0x8(%r11)
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_1b4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_28c:
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_296:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_29b:
  nop
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2a5:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2aa:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_2b0:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_0:
  lea -0x30(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_47b
  push %rbp
  mov %rsp,%rbp
  sub $0xa8,%rsp
  mov %rbx,0xc0(%rsp)
  cmp $0xe4,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_268
  mov (%rbx),%edx
  nop
  nop
  nop
  nop
  cmp $0xe4,%rdx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_251
  lea -0xe4(%rdi),%rdx
  mov %rdx,%rsi
  neg %rdx
  sar $0x3f,%rdx
  and $0xe4,%edx
  add $-0xe4,%rcx
  add %rbx,%rdx
  test $0x7,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1a2
  shr $0x3,%rcx
  nop
  cmp $0x800,%rcx
  jg L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_105
  mov %rax,0xb8(%rsp)
  mov %rdi,0xd0(%rsp)
  mov %rsi,0x38(%rsp)
  mov %rdx,0x40(%rsp)
  mov %rcx,0x28(%rsp)
  mov %rbx,0xc0(%rsp)
  lea type__+387456(%rip),%rax
  mov %rcx,%rbx
  callq runtime.makeslice
  mov 0x28(%rsp),%rdx
  mov 0xb8(%rsp),%rsi
  mov %rdx,0x10(%rsi)
  mov %rdx,0x18(%rsi)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_ed
  mov 0x8(%rsi),%rcx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_ed:
  mov %rax,0x8(%rsi)
  mov 0x38(%rsp),%rcx
  mov 0x40(%rsp),%rbx
  xor %eax,%eax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_28a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_105:
  lea 0x60(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x60(%rsp)
  mov %rax,0x68(%rsp)
  mov ssz.ErrListTooBig(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_13c
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_13c:
  mov ssz.ErrListTooBig+8(%rip),%rdx
  mov %rcx,0x70(%rsp)
  mov %rdx,0x78(%rsp)
  lea go_string._+163839(%rip),%rax
  mov $0x49,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_199
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x49,0x8(%rax)
  lea go_string._+163839(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_199:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1a2:
  lea 0x80(%rsp),%rdx
  movups %xmm15,(%rdx)
  movups %xmm15,0x10(%rdx)
  mov %rcx,%rax
  callq runtime.convT64
  lea type__+387520(%rip),%rcx
  mov %rcx,0x80(%rsp)
  mov %rax,0x88(%rsp)
  mov ssz.ErrIncorrectListSize(%rip),%rcx
  test %rcx,%rcx
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1e2
  mov 0x8(%rcx),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_1e2:
  mov ssz.ErrIncorrectListSize+8(%rip),%rdx
  mov %rcx,0x90(%rsp)
  mov %rdx,0x98(%rsp)
  lea go_string._+171319(%rip),%rax
  mov $0x53,%ebx
  lea 0x80(%rsp),%rcx
  mov $0x2,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_248
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x53,0x8(%rax)
  lea go_string._+171319(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_248:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_251:
  mov ssz.ErrInvalidVariableOffset(%rip),%rax
  mov ssz.ErrInvalidVariableOffset+8(%rip),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_268:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_27f:
  mov 0x8(%rsi),%rdi
  mov %r10,(%rdi,%r9,8)
  mov %r8,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_28a:
  cmp %rdx,%rax
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2cc
  lea 0x1(%rax),%rdi
  mov %rdi,%r8
  shl $0x3,%rdi
  nop
  cmp %rcx,%rdi
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_475
  mov %rax,%r9
  shl $0x3,%rax
  cmp %rax,%rdi
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_470
  mov 0x10(%rsi),%rdi
  nop
  mov (%rbx,%r9,8),%r10
  cmp %rdi,%r9
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_27f
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_46b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2cc:
  lea type__+1464512(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2ec
  mov 0xb8(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_304
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_2ec:
  mov 0xb8(%rsp),%rdx
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_304:
  mov %rax,0x20(%rdx)
  mov 0xc0(%rsp),%rbx
  add $0x4,%rbx
  mov 0xd0(%rsp),%rdi
  add $-0x4,%rdi
  mov $0x80,%ecx
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_39c
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_33b
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_33b:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+15010(%rip),%rax
  mov $0x8,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_393
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+15010(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_393:
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_39c:
  mov %rbx,0x48(%rsp)
  mov %rax,0x30(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0xb8(%rsp),%rdx
  movq $0x0,0x30(%rdx)
  movq $0x60,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_3ec
  mov 0x28(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_3ec:
  mov %rax,0xa0(%rsp)
  mov %rax,0x28(%rdx)
  mov 0xc0(%rsp),%rbx
  add $0x84,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0xb8(%rsp),%rdx
  movq $0x60,0x30(%rdx)
  movq $0x60,0x38(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_43c
  mov 0xa0(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_454
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_43c:
  mov 0x28(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0xa0(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_454:
  mov %rsi,0x28(%rdx)
  mov 0x30(%rsp),%rax
  mov 0x48(%rsp),%rbx
  add $0xa8,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_46b:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_470:
  callq runtime.panicBounds
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_475:
  callq runtime.panicBounds
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_47b:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_20d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov (%rax),%rdx
  cmpq $0x20,0x8(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1f2
  mov %rax,0x60(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_6b:
  mov %rbx,0x48(%rsp)
  mov %r8,0x38(%rsp)
  mov %rdi,0x30(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x18(%rdx),%rbx
  cmpq $0x20,0x20(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1d7
  mov 0x38(%rsp),%r8
  lea 0x20(%r8),%r9
  mov 0x30(%rsp),%rcx
  cmp %r9,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r9,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%r8
  mov %rbx,%r9
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %r9,0x38(%rsp)
  mov %rcx,0x30(%rsp)
  add %r8,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x30(%rdx),%rbx
  cmpq $0x20,0x38(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1bc
  mov 0x38(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x30(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_133
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_15e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_133:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x38(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_15e:
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rax,0x48(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1a3
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1b2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1a3:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1b2:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1bc:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1d7:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_1f2:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_20d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_224
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x60,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_210
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x20,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_74:
  mov %rax,0x18(%rsp)
  mov %rax,(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x8(%rdx)
  movq $0x20,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_b0
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_c4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_b0:
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_c4:
  mov %rdi,(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_10c
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x20,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_14d:
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_162:
  mov %rdi,0x18(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_1ac
  mov 0x30(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_1ac:
  mov %rax,0x18(%rsp)
  mov %rax,0x30(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x40,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x38(%rdx)
  movq $0x20,0x40(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_1ed
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_202
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_1ed:
  mov 0x30(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_202:
  mov %rsi,0x30(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_210:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_224:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_17d
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  mov (%rax),%rdx
  cmpq $0x20,0x8(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_162
  mov %rax,0x60(%rsp)
  lea 0x20(%rcx),%r8
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_6b
  mov %rcx,0x70(%rsp)
  mov %rdx,0x48(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x48(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0x70(%rsp),%rcx
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_6b:
  mov %rdi,0x38(%rsp)
  mov %r8,0x30(%rsp)
  mov %rbx,0x48(%rsp)
  lea (%rbx,%rcx,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rdx
  mov 0x18(%rdx),%rbx
  cmpq $0x20,0x20(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_147
  mov 0x30(%rsp),%rdx
  lea 0x20(%rdx),%r8
  mov 0x38(%rsp),%rcx
  cmp %r8,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_b9
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_e4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_b9:
  mov %rbx,0x40(%rsp)
  mov 0x48(%rsp),%rax
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x30(%rsp),%rdx
  mov %rbx,%r8
  mov 0x40(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_e4:
  mov %rax,0x48(%rsp)
  mov %rcx,0x38(%rsp)
  mov %r8,0x30(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  nop
  callq runtime.memmove
  mov 0x48(%rsp),%rbx
  mov %rbx,%rdx
  sub %rsp,%rdx
  lea 0x60(%rsp),%rsi
  sub %rsp,%rsi
  cmp %rsi,%rdx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_12e
  mov 0x30(%rsp),%rbx
  mov 0x38(%rsp),%rcx
  mov 0x48(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_13d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_12e:
  mov $0x1,%eax
  mov 0x30(%rsp),%rcx
  callq runtime.moveSliceNoCapNoScan
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_13d:
  xor %edi,%edi
  xor %esi,%esi
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_147:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_162:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_17d:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_184
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x40,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_170
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x8(%rdx)
  movq $0x20,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_74
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_74:
  mov %rax,0x18(%rsp)
  mov %rax,(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x8(%rdx)
  movq $0x20,0x10(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_b0
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_c4
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_b0:
  mov (%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_c4:
  mov %rdi,(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_10c
  mov 0x18(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x18(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x20,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x20(%rdx)
  movq $0x20,0x28(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_14d:
  mov 0x18(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_162:
  mov %rsi,0x18(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_170:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_184:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_0:
  lea -0x38(%rsp),%r12
  cmp 0x10(%r14),%r12
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2c6
  push %rbp
  mov %rsp,%rbp
  sub $0xb0,%rsp
  mov %rbx,0xc8(%rsp)
  mov 0x8(%rax),%rdx
  cmpq $0x4,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2a8
  mov %rax,0xc0(%rsp)
  lea 0x4(%rcx),%r8
  nop
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_90
  mov %rcx,0xd0(%rsp)
  mov %rdx,0xa8(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x4,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov 0xd0(%rsp),%rcx
  mov %rax,%rbx
  mov 0xc0(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_90:
  mov (%rdx),%edx
  mov %edx,(%rbx,%rcx,1)
  mov 0x20(%rax),%rdx
  cmpq $0x20,0x28(%rax)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_28a
  lea 0x20(%r8),%r9
  cmp %r9,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_ec
  mov %rdx,0xa8(%rsp)
  mov %r8,0x50(%rsp)
  mov %rbx,%rax
  mov %r9,%rbx
  mov %rdi,%rcx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xa8(%rsp),%rdx
  mov 0x50(%rsp),%r8
  mov %rcx,%rdi
  mov %rbx,%r9
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_ec:
  mov %rdi,0x48(%rsp)
  mov %r9,0x38(%rsp)
  mov %rbx,0xa0(%rsp)
  lea (%rbx,%r8,1),%rax
  mov %rdx,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x38(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xc0(%rsp),%rsi
  mov 0x38(%rsi),%rdi
  nop
  nop
  nop
  lea 0x78(%rsp),%r8
  movups %xmm15,(%r8)
  movups %xmm15,0x10(%r8)
  mov %rdi,0x78(%rsp)
  mov 0x48(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_14f
  mov 0xa0(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_17b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_14f:
  mov 0xa0(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0xc0(%rsp),%rsi
  mov %rbx,%rdx
  mov 0x38(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_17b:
  mov 0x78(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov 0x40(%rsi),%rbx
  cmpq $0x20,0x48(%rsi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_26c
  lea 0x20(%rdx),%r8
  cmp %r8,%rcx
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_1cd
  mov %rdx,0x28(%rsp)
  mov %rbx,0xa8(%rsp)
  mov %r8,%rbx
  mov $0x20,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rbx,%r8
  mov 0xa8(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_1cd:
  mov %r8,0x30(%rsp)
  mov %rcx,0x40(%rsp)
  mov %rax,0x98(%rsp)
  add %rdx,%rax
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rbx
  lea 0x8(%rbx),%rdx
  mov 0xc0(%rsp),%rsi
  mov 0x58(%rsi),%rsi
  nop
  nop
  nop
  lea 0x58(%rsp),%rdi
  movups %xmm15,(%rdi)
  movups %xmm15,0x10(%rdi)
  mov %rsi,0x58(%rsp)
  mov 0x40(%rsp),%rcx
  nop
  cmp %rdx,%rcx
  jb L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_22f
  mov 0x98(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_253
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_22f:
  mov 0x98(%rsp),%rax
  mov %rdx,%rbx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rbx,%rdx
  mov 0x30(%rsp),%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_253:
  mov 0x58(%rsp),%r8
  mov %r8,(%rax,%rbx,1)
  mov %rdx,%rbx
  xor %edi,%edi
  xor %esi,%esi
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_26c:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_28a:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2a8:
  mov ssz.ErrBytesLength(%rip),%rdi
  mov ssz.ErrBytesLength+8(%rip),%rsi
  xor %eax,%eax
  xor %ebx,%ebx
  mov %rbx,%rcx
  add $0xb0,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_2c6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_32e
  push %rbp
  mov %rsp,%rbp
  sub $0x50,%rsp
  mov %rbx,0x68(%rsp)
  nop
  cmp $0x54,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_31a
  mov %rax,0x60(%rsp)
  mov %rdi,0x78(%rsp)
  mov %rbx,0x68(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x4,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_7a
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_7a:
  mov %rax,0x8(%rdx)
  mov 0x68(%rsp),%rsi
  mov (%rsi),%edi
  mov %edi,(%rax)
  movq $0x4,0x10(%rdx)
  movq $0x4,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_b2
  mov 0x8(%rdx),%rdi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_b2:
  mov %rax,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_f7
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_f7:
  mov %rax,0x28(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x4,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x20,0x28(%rax)
  movq $0x20,0x30(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_138
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_151
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_138:
  mov 0x20(%rax),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_151:
  mov %rsi,0x20(%rax)
  mov 0x68(%rsp),%rbx
  add $0x24,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x24,%rdi
  add $0x38,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e7
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_186
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_186:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+43515(%rip),%rax
  mov $0x12,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43515(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e1:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_1e7:
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x60(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x20,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_22c
  mov 0x40(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_22c:
  mov %rax,0x28(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x68(%rsp),%rbx
  add $0x2c,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x60(%rsp),%rax
  movq $0x20,0x48(%rax)
  movq $0x20,0x50(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_26d
  mov 0x28(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_282
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_26d:
  mov 0x40(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x28(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_282:
  mov %rsi,0x40(%rax)
  mov 0x68(%rsp),%rbx
  add $0x4c,%rbx
  mov 0x78(%rsp),%rdi
  add $-0x4c,%rdi
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Slot.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_314
  movups %xmm15,0x30(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_2b7
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_2b7:
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea go_string._+26459(%rip),%rax
  mov $0xc,%ebx
  lea 0x30(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_30e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0xc,0x8(%rax)
  lea go_string._+26459(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_30e:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_314:
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_31a:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x50,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_32e:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.UnmarshalSSZ_0
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_455
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  nop
  cmp $0x79,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_441
  mov %rax,0x80(%rsp)
  mov %rdi,0x98(%rsp)
  mov %rbx,0x88(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_86
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_86:
  mov %rax,0x68(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x88(%rsp),%rbx
  mov $0x30,%ecx
  nop
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_cd
  mov 0x68(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_e2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_cd:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x68(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_e2:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_12c
  mov 0x20(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_12c:
  mov %rax,0x68(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x80(%rsp),%rax
  movq $0x20,0x28(%rax)
  movq $0x20,0x30(%rax)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_173
  mov 0x68(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_188
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_173:
  mov 0x20(%rax),%rdx
  callq runtime.gcWriteBarrier2
  mov 0x68(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_188:
  mov %rsi,0x20(%rax)
  mov 0x88(%rsp),%rbx
  mov 0x50(%rbx),%rdx
  mov %rdx,0x38(%rax)
  movzbl 0x58(%rbx),%edx
  cmp $0x1,%dl
  ja L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_42d
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b1
  movb $0x1,0x40(%rax)
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b5
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b1:
  movb $0x0,0x40(%rax)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1b5:
  add $0x59,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x59,%rdi
  add $0x48,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_247
  movups %xmm15,0x58(%rsp)
  nop
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1e6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_1e6:
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  lea go_string._+79927(%rip),%rax
  mov $0x1e,%ebx
  lea 0x58(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_241
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x1e,0x8(%rax)
  lea go_string._+79927(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_241:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_247:
  mov 0x88(%rsp),%rbx
  add $0x61,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x61,%rdi
  mov 0x80(%rsp),%rax
  add $0x50,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e7
  movups %xmm15,0x48(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_286
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_286:
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  lea go_string._+46529(%rip),%rax
  mov $0x13,%ebx
  lea 0x48(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x13,0x8(%rax)
  lea go_string._+46529(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e1:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_2e7:
  mov 0x88(%rsp),%rbx
  add $0x69,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x69,%rdi
  mov 0x80(%rsp),%rax
  add $0x58,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_387
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_326
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_326:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+29272(%rip),%rax
  mov $0xd,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_381
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xd,0x8(%rax)
  lea go_string._+29272(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_381:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_387:
  mov 0x88(%rsp),%rbx
  add $0x71,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x71,%rdi
  mov 0x80(%rsp),%rax
  add $0x60,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_427
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_3c6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_3c6:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+52923(%rip),%rax
  mov $0x15,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_421
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x15,0x8(%rax)
  lea go_string._+52923(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_421:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_427:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_42d:
  mov ssz.ErrInvalidSerialization(%rip),%rax
  mov ssz.ErrInvalidSerialization+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_441:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_455:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_d6
  push %rbp
  mov %rsp,%rbp
  sub $0x68,%rsp
  mov %rbx,0x80(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x48(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x48(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_7b
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
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_7b:
  mov 0x48(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  add $0x8,%rdx
  mov 0x10(%rax),%r8
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_be
  mov %r8,0x40(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x40(%rsp),%r8
  mov %rbx,%rdx
  mov %rcx,%rdi
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_be:
  mov %r8,-0x8(%rdx,%rbx,1)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x68,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_d6:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_e1
  push %rbp
  mov %rsp,%rbp
  sub $0x38,%rsp
  mov %rbx,0x50(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_cc
  mov %rax,0x48(%rsp)
  mov %rbx,0x50(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_b4
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_56
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_56:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+18141(%rip),%rax
  mov $0x9,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_ae
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18141(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_ae:
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_b4:
  mov 0x50(%rsp),%rcx
  mov 0x8(%rcx),%rcx
  mov 0x48(%rsp),%rdx
  mov %rcx,0x10(%rdx)
  add $0x38,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_cc:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x38,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_e1:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.UnmarshalSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_f5
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  lea 0x8(%rcx),%rdx
  mov 0x8(%rax),%r8
  nop
  nop
  nop
  lea 0x50(%rsp),%r9
  movups %xmm15,(%r9)
  movups %xmm15,0x10(%r9)
  mov %r8,0x50(%rsp)
  cmp %rdx,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_80
  mov %rax,0x80(%rsp)
  mov %rcx,0x90(%rsp)
  mov %rbx,%rax
  mov %rdx,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov %rcx,%rdi
  mov %rbx,%rdx
  mov 0x90(%rsp),%rcx
  mov %rax,%rbx
  mov 0x80(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_80:
  mov 0x50(%rsp),%r8
  mov %r8,(%rbx,%rcx,1)
  lea 0x8(%rdx),%r8
  mov 0x10(%rax),%r9
  nop
  nop
  nop
  lea 0x30(%rsp),%r10
  movups %xmm15,(%r10)
  movups %xmm15,0x10(%r10)
  mov %r9,0x30(%rsp)
  cmp %r8,%rdi
  jae L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_d9
  mov %rdx,0x28(%rsp)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  mov $0x8,%edi
  lea type__+387072(%rip),%rsi
  callq runtime.growslice
  mov 0x28(%rsp),%rdx
  mov %rcx,%rdi
  mov %rbx,%r8
  mov %rax,%rbx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_d9:
  mov 0x30(%rsp),%r9
  mov %r9,(%rbx,%rdx,1)
  mov %rbx,%rax
  mov %r8,%rbx
  mov %rdi,%rcx
  xor %edi,%edi
  xor %esi,%esi
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_f5:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.MarshalSSZTo_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_167
  push %rbp
  mov %rsp,%rbp
  sub $0x48,%rsp
  mov %rbx,0x60(%rsp)
  nop
  cmp $0x10,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_153
  mov %rax,0x58(%rsp)
  mov %rbx,0x60(%rsp)
  mov %rdi,0x70(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.Epoch.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_b9
  movups %xmm15,0x38(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_5a
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_5a:
  mov %rax,0x38(%rsp)
  mov %rbx,0x40(%rsp)
  lea go_string._+18159(%rip),%rax
  mov $0x9,%ebx
  lea 0x38(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  nop
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_b3
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x9,0x8(%rax)
  lea go_string._+18159(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_b3:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_b9:
  mov 0x60(%rsp),%rbx
  add $0x8,%rbx
  mov 0x70(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x58(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  nop
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_14d
  movups %xmm15,0x28(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_f1
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_f1:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea go_string._+43461(%rip),%rax
  mov $0x12,%ebx
  lea 0x28(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_147
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x12,0x8(%rax)
  lea go_string._+43461(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_147:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_14d:
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_153:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x48,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_167:
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
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.UnmarshalSSZ_0
