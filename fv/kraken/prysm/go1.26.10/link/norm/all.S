github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.SizeSSZ:
  mov $0x74,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.DepositRequest.SizeSSZ:
  mov $0xc0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ExecutionPayloadHeader.SizeSSZ:
  mov 0xc0(%rax),%rax
  add $0x218,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ExecutionPayloadHeaderCapella.SizeSSZ:
  mov 0xc0(%rax),%rax
  add $0x238,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ExecutionPayloadHeaderDeneb.SizeSSZ:
  mov 0xc0(%rax),%rax
  add $0x248,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.ExecutionRequests.SizeSSZ:
  mov 0x10(%rax),%rcx
  lea (%rcx,%rcx,2),%rcx
  shl $0x6,%rcx
  mov 0x28(%rax),%rdx
  imul $0x4c,%rdx,%rdx
  add %rdx,%rcx
  mov 0x40(%rax),%rdx
  imul $0x74,%rdx,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0xc(%rax),%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.Withdrawal.SizeSSZ:
  mov $0x2c,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_engine_v1.WithdrawalRequest.SizeSSZ:
  mov $0x4c,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1597792(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockAltair.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_195
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x17c,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  lea (%rdx,%rcx,1),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_195:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateAltair.SizeSSZ:
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rax
  lea 0x29c1f5(%rax),%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ContributionAndProof.SizeSSZ:
  mov $0x108,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderAltair.SizeSSZ:
  mov $0x70,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapAltair.SizeSSZ:
  mov $0x6140,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateAltair.SizeSSZ:
  mov $0x6318,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateAltair.SizeSSZ:
  mov $0x248,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateAltair.SizeSSZ:
  mov $0x118,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1465088(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1597792(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyAltair.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockAltair.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedContributionAndProof.SizeSSZ:
  mov $0x168,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregate.SizeSSZ:
  mov $0xa0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncAggregatorSelectionData.SizeSSZ:
  mov $0x10,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommittee.SizeSSZ:
  mov $0x6030,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeContribution.SizeSSZ:
  mov $0xa0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SyncCommitteeMessage.SizeSSZ:
  mov $0x90,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1612928(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_22f
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x180,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1660384(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  mov 0xc0(%rdx),%rbx
  mov 0x100(%rdx),%rsi
  add $0x1fc,%rbx
  mov 0x108(%rdx),%rdx
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_220
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_207:
  mov %rsi,%rdi
  mov 0x8(%rdi),%rdi
  lea (%rbx,%rdi,1),%rbx
  lea 0x4(%rbx),%rbx
  add $0x18,%rsi
  inc %rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_220:
  cmp %rdx,%rax
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_207
  lea (%rcx,%rbx,1),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_22f:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_d7
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  cmpq $0x0,0x190(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_bc
  mov %rax,0x28(%rsp)
  mov %rcx,0x10(%rsp)
  lea type__+1659872(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_ad
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x190(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_ad:
  mov %rax,0x190(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_bc:
  mov 0x190(%rax),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x29c411(%rcx),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_d7:
  mov %rax,0x8(%rsp)
  nop
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1613344(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1fb
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x180,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1659872(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x218(%rcx),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_1fb:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1465376(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1612928(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1465664(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1613344(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyBellatrix.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockBellatrix.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_24e
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x184,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1671424(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  mov 0xc0(%rdx),%rbx
  mov 0x100(%rdx),%rsi
  add $0x200,%rbx
  mov 0x108(%rdx),%rdi
  xor %r8d,%r8d
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_220
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_208:
  mov %rsi,%r9
  mov 0x8(%r9),%r9
  lea (%rbx,%r9,1),%rbx
  lea 0x4(%rbx),%rbx
  add $0x18,%rsi
  inc %r8
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_220:
  cmp %rdi,%r8
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_208
  mov 0xd0(%rax),%rsi
  imul $0xac,%rsi,%rsi
  mov 0x120(%rdx),%rdx
  imul $0x2c,%rdx,%rdx
  add %rbx,%rdx
  add %rdx,%rcx
  lea (%rsi,%rcx,1),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_24e:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1626528(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_e6
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  cmpq $0x0,0x190(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_bc
  mov %rax,0x28(%rsp)
  mov %rcx,0x10(%rsp)
  lea type__+1670880(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_ad
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x190(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_ad:
  mov %rax,0x190(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_bc:
  mov 0x190(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0x1b0(%rax),%rdx
  shl $0x6,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x29c445(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_e6:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_20d
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x184,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0xd0(%rax),%rdx
  imul $0xac,%rdx,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0x238(%rax),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_20d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1626080(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BLSToExecutionChange.SizeSSZ:
  mov $0x4c,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_6a
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_4c:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_53:
  mov 0x8(%rax),%rcx
  mov 0xc0(%rcx),%rax
  add $0x28c,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_6a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalSummary.SizeSSZ:
  mov $0x40,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1383616(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x6400,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_56
  lea type__+1383616(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_f8
  lea type__+1383616(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_ec:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_f8:
  mov 0x10(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x7c8(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_6a
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_4c:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_53:
  mov 0x10(%rax),%rcx
  mov 0xc0(%rcx),%rax
  add $0x32c,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_6a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1383616(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x3d8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_56
  lea type__+1383616(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x30(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_f8
  lea type__+1383616(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x30(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_ec:
  mov %rax,0x30(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_f8:
  mov 0x30(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x6898(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1467104(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1626528(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyCapella.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1465952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1626080(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyCapella.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBLSToExecutionChange.SizeSSZ:
  mov $0xac,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1385920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x8(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1670880(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_98:
  mov %rax,0x8(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_9c:
  mov 0x8(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x2f0,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidCapella.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_261
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x188,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1682112(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  mov 0xc0(%rdx),%rbx
  mov 0x100(%rdx),%rsi
  add $0x210,%rbx
  mov 0x108(%rdx),%rdi
  xor %r8d,%r8d
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_220
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_208:
  mov %rsi,%r9
  mov 0x8(%r9),%r9
  lea (%rbx,%r9,1),%rbx
  lea 0x4(%rbx),%rbx
  add $0x18,%rsi
  inc %r8
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_220:
  cmp %rdi,%r8
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_208
  mov 0xd0(%rax),%rsi
  imul $0xac,%rsi,%rsi
  mov 0xe8(%rax),%rdi
  lea (%rdi,%rdi,2),%rdi
  shl $0x4,%rdi
  mov 0x120(%rdx),%rdx
  imul $0x2c,%rdx,%rdx
  add %rbx,%rdx
  add %rdx,%rcx
  add %rsi,%rcx
  lea (%rdi,%rcx,1),%rax
  add $0x40,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_261:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_cf
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_56
  lea type__+1467392(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1636960(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ
  mov 0x28(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0x60(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_cf:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1636960(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_e6
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  cmpq $0x0,0x190(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_bc
  mov %rax,0x28(%rsp)
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_ad
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x190(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_ad:
  mov %rax,0x190(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_bc:
  mov 0x190(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0x1b0(%rax),%rdx
  shl $0x6,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x29c455(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_e6:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_21f
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x188,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0xd0(%rax),%rdx
  imul $0xac,%rdx,%rdx
  add %rdx,%rcx
  mov 0xe8(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x248(%rax),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_21f:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1636000(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobIdentifier.SizeSSZ:
  mov $0x28,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecar.SizeSSZ:
  mov $0x20358,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlobSidecars.SizeSSZ:
  mov 0x10(%rax),%rcx
  imul $0x20358,%rcx,%rax
  add $0x4,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_76
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_4c:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_53:
  mov 0x8(%rax),%rcx
  mov 0x18(%rax),%rdx
  lea (%rdx,%rdx,2),%rax
  shl $0x4,%rax
  add 0xc0(%rcx),%rax
  add $0x2a0,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_76:
  mov %rax,0x8(%rsp)
  nop
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_6a
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_4c:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_53:
  mov 0x10(%rax),%rcx
  mov 0xc0(%rcx),%rax
  add $0x33c,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_6a:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientHeaderDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x6410,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_56
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x30(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_f8
  lea type__+1382592(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x30(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_ec:
  mov %rax,0x30(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_f8:
  mov 0x30(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x68b8(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_56
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_f8
  lea type__+1382592(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_ec:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_f8:
  mov 0x10(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x7e8(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x3e8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientOptimisticUpdateDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_89
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  mov %rax,0x20(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_56
  lea type__+1297152(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_3a
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_3a:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ
  mov 0x20(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0xc(%rax),%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_89:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1467392(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1636960(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyDeneb.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1466240(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1636000(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyDeneb.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_bf
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1431168(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x8(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_98:
  mov %rax,0x8(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_9c:
  mov 0x8(%rcx),%rdx
  mov 0x18(%rcx),%rcx
  lea (%rcx,%rcx,2),%rax
  shl $0x4,%rax
  add 0xc0(%rdx),%rax
  add $0x304,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_bf:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidDeneb.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_67
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1422240(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_4c:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_53:
  mov 0x10(%rax),%rcx
  mov 0x10(%rcx),%rax
  add $0x158,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_67:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProofElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationElectra.SizeSSZ:
  mov 0x10(%rax),%rax
  add $0xec,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_c1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_56
  lea type__+1369024(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  mov 0x10(%rcx),%rcx
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_a7
  mov %rcx,0x10(%rsp)
  lea type__+1369024(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_86
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_9b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_86:
  mov 0x28(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_9b:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_a7:
  mov 0x10(%rax),%rdx
  add 0x10(%rdx),%rcx
  shl $0x3,%rcx
  lea 0x1d0(%rcx),%rax
  add $0x18,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_c1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashingElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_2e2
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x18c,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_ce
  lea type__+1369024(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1369024(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xf0(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1682112(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  mov 0xc0(%rdx),%rbx
  mov 0x100(%rdx),%rsi
  add $0x210,%rbx
  mov 0x108(%rdx),%rdi
  xor %r8d,%r8d
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_220
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_208:
  mov %rsi,%r9
  mov 0x8(%r9),%r9
  lea (%rbx,%r9,1),%rbx
  lea 0x4(%rbx),%rbx
  add $0x18,%rsi
  inc %r8
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_220:
  cmp %rdi,%r8
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_208
  mov 0xd0(%rax),%rsi
  imul $0xac,%rsi,%rsi
  mov 0xe8(%rax),%rdi
  lea (%rdi,%rdi,2),%rdi
  shl $0x4,%rdi
  mov 0x120(%rdx),%rdx
  imul $0x2c,%rdx,%rdx
  add %rbx,%rdx
  add %rdx,%rcx
  add %rsi,%rcx
  add %rdi,%rcx
  cmpq $0x0,0xf8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_2ab
  mov %rcx,0x10(%rsp)
  lea type__+1365952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_284
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_29c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_284:
  mov 0x50(%rsp),%rcx
  mov 0xf8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_29c:
  mov %rax,0xf8(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_2ab:
  mov 0xf8(%rax),%rdx
  mov 0x10(%rdx),%rbx
  lea (%rbx,%rbx,2),%rbx
  shl $0x6,%rbx
  mov 0x28(%rdx),%rsi
  imul $0x4c,%rsi,%rsi
  add %rsi,%rbx
  mov 0x40(%rdx),%rdx
  imul $0x74,%rdx,%rdx
  add %rbx,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0xc(%rax),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_2e2:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_cf
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_56
  lea type__+1467680(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ
  mov 0x28(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0x60(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_cf:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1649920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_115
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  cmpq $0x0,0x190(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_bc
  mov %rax,0x28(%rsp)
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_ad
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x190(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_ad:
  mov %rax,0x190(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_bc:
  mov 0x190(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0x1b0(%rax),%rdx
  shl $0x6,%rdx
  add %rdx,%rcx
  mov 0x1f8(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x6,%rdx
  add %rdx,%rcx
  mov 0x210(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x228(%rax),%rdx
  shl $0x4,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x29c491(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_115:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_29d
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x18c,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_ce
  lea type__+1369024(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1369024(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xf0(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0xd0(%rax),%rdx
  imul $0xac,%rdx,%rdx
  add %rdx,%rcx
  mov 0xe8(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xf8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_263
  mov %rcx,0x28(%rsp)
  lea type__+1365952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_23c
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_254
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_23c:
  mov 0x50(%rsp),%rcx
  mov 0xf8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_254:
  mov %rax,0xf8(%rcx)
  mov %rcx,%rax
  mov 0x28(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_263:
  mov 0xf8(%rax),%rdx
  mov 0x10(%rdx),%rbx
  lea (%rbx,%rbx,2),%rbx
  shl $0x6,%rbx
  mov 0x28(%rdx),%rsi
  imul $0x4c,%rsi,%rsi
  add %rsi,%rbx
  mov 0x40(%rdx),%rdx
  imul $0x74,%rdx,%rdx
  add %rbx,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x254(%rax),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_29d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1649440(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_ef
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_56
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  mov 0x18(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add 0xc0(%rcx),%rdx
  cmpq $0x0,0x28(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_b8
  mov %rdx,0x10(%rsp)
  lea type__+1365952(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x28(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_ac:
  mov %rax,0x28(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rdx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_b8:
  mov 0x28(%rax),%rcx
  mov 0x10(%rcx),%rbx
  lea (%rbx,%rbx,2),%rbx
  shl $0x6,%rbx
  mov 0x28(%rcx),%rsi
  imul $0x4c,%rsi,%rsi
  add %rsi,%rbx
  mov 0x40(%rcx),%rcx
  imul $0x74,%rcx,%rcx
  add %rbx,%rcx
  lea (%rcx,%rdx,1),%rax
  lea 0x2b0(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_ef:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestationElectra.SizeSSZ:
  mov 0x10(%rax),%rax
  shl $0x3,%rax
  add $0xe4,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_b3
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rax
  add $0x6430,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_b3:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientBootstrapElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_56
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x30(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_f8
  lea type__+1382592(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x30(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_ec:
  mov %rax,0x30(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_f8:
  mov 0x30(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x68f8(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientUpdateElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_15d
  push %rbp
  mov %rsp,%rbp
  sub $0x28,%rsp
  mov %rax,0x38(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_56
  lea type__+1382592(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_3a
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_3a:
  mov 0x38(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_a1
  mov %rcx,0x20(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_83
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_83:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_98:
  mov %rax,0x10(%rcx)
  mov 0x38(%rsp),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_a1:
  mov 0x10(%rcx),%rcx
  mov 0xc0(%rcx),%rcx
  mov %rcx,0x10(%rsp)
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_f8
  lea type__+1382592(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_d5
  mov 0x38(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_ec
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_d5:
  mov 0x38(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_ec:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_f8:
  mov 0x10(%rax),%rdx
  cmpq $0x0,0x10(%rdx)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_145
  mov %rdx,0x18(%rsp)
  lea type__+1682688(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_124
  mov 0x18(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_139
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_124:
  mov 0x18(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_139:
  mov %rax,0x10(%rcx)
  mov %rcx,%rdx
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_145:
  mov 0x10(%rdx),%rdx
  add 0xc0(%rdx),%rcx
  lea 0x808(%rcx),%rax
  add $0x28,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_15d:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.LightClientFinalityUpdateElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingDeposit.SizeSSZ:
  mov $0xc0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingConsolidation.SizeSSZ:
  mov $0x10,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingPartialWithdrawal.SizeSSZ:
  mov $0x18,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_b0
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1373888(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1422240(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0x10(%rcx),%rax
  add $0x1bc,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_b0:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProofElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_89
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  mov %rax,0x20(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_56
  lea type__+1297376(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_3a
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_3a:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_56:
  mov 0x8(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ
  mov 0x20(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0xc(%rax),%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_89:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1467680(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1466528(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649440(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1474016(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_4c:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_53:
  mov 0x8(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BuilderBidElectra.SizeSSZ
  add $0x64,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBuilderBidElectra.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.SizeSSZ:
  mov $0xf0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_cf
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_56
  lea type__+1467680(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ
  mov 0x28(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0x60(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_cf:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockContentsFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_115
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  cmpq $0x0,0x190(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_bc
  mov %rax,0x28(%rsp)
  mov %rcx,0x10(%rsp)
  lea type__+1682688(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_95
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_ad
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_95:
  mov 0x28(%rsp),%rcx
  mov 0x190(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_ad:
  mov %rax,0x190(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_bc:
  mov 0x190(%rax),%rdx
  add 0xc0(%rdx),%rcx
  mov 0x1b0(%rax),%rdx
  shl $0x6,%rdx
  add %rdx,%rcx
  mov 0x1f8(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x6,%rdx
  add %rdx,%rcx
  mov 0x210(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x228(%rax),%rdx
  shl $0x4,%rdx
  lea (%rdx,%rcx,1),%rax
  lea 0x29c691(%rax),%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_115:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1649440(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnSidecar.SizeSSZ:
  mov 0x18(%rax),%rcx
  shl $0xb,%rcx
  mov 0x30(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rdx,%rcx
  mov 0x48(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0x164(%rax),%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnsByRootIdentifier.SizeSSZ:
  mov 0x28(%rax),%rax
  shl $0x3,%rax
  add $0x24,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnHeader.SizeSSZ:
  mov 0x10(%rax),%rcx
  lea (%rcx,%rcx,2),%rax
  shl $0x4,%rax
  add $0x154,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnPartsMetadata.SizeSSZ:
  mov 0x10(%rax),%rcx
  add 0x28(%rax),%rcx
  lea 0x8(%rcx),%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnSidecar.SizeSSZ:
  mov 0x28(%rax),%rcx
  shl $0xb,%rcx
  add 0x10(%rax),%rcx
  mov 0x40(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  lea (%rcx,%rdx,1),%rcx
  lea 0x10(%rcx),%rcx
  mov 0x58(%rax),%rdx
  mov 0x50(%rax),%rbx
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnSidecar.SizeSSZ_4a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnSidecar.SizeSSZ_2c:
  mov (%rbx,%rax,8),%rsi
  mov 0x10(%rsi),%rsi
  lea (%rsi,%rsi,2),%rsi
  shl $0x4,%rsi
  lea (%rsi,%rcx,1),%rcx
  lea 0x158(%rcx),%rcx
  inc %rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnSidecar.SizeSSZ_4a:
  cmp %rdx,%rax
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PartialDataColumnSidecar.SizeSSZ_2c
  mov %rcx,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_89
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  mov %rax,0x20(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_56
  lea type__+1297600(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_3a
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_3a:
  mov 0x20(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_56:
  mov 0x8(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ
  mov 0x20(%rsp),%rcx
  mov 0x18(%rcx),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rax,%rdx
  mov 0x30(%rcx),%rcx
  shl $0x11,%rcx
  lea (%rdx,%rcx,1),%rax
  lea 0xc(%rax),%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_89:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockContentsFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1467680(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649920(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyElectra.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1466816(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1649440(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BlindedBeaconBlockBodyElectra.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBlindedBeaconBlockFulu.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.StatusV2.SizeSSZ:
  mov $0x5c,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_67
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1368512(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_4c:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_53:
  mov 0x10(%rax),%rcx
  mov 0x10(%rcx),%rax
  add $0x150,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_67:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AggregateAttestationAndProof.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Attestation.SizeSSZ:
  mov 0x10(%rax),%rax
  add $0xe4,%rax
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_c1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  mov %rax,0x28(%rsp)
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_56
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  mov 0x10(%rcx),%rcx
  cmpq $0x0,0x10(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_a7
  mov %rcx,0x10(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_86
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_9b
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_86:
  mov 0x28(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_9b:
  mov %rax,0x10(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_a7:
  mov 0x10(%rax),%rdx
  add 0x10(%rdx),%rcx
  shl $0x3,%rcx
  lea 0x1d0(%rcx),%rax
  add $0x18,%rsp
  pop %rbp
  nop
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_c1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttesterSlashing.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_66
  push %rbp
  mov %rsp,%rbp
  sub $0x10,%rsp
  cmpq $0x0,0x48(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_53
  mov %rax,0x20(%rsp)
  lea type__+1576736(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_36
  mov 0x20(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_4c
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_36:
  mov 0x20(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_4c:
  mov %rax,0x48(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_53:
  mov 0x48(%rax),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ
  add $0x54,%rax
  add $0x10,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_66:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlock.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_195
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0xdc,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  lea (%rdx,%rcx,1),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_195:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockHeader.SizeSSZ:
  mov $0x70,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ:
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  lea 0x290191(%rcx),%rcx
  mov 0x110(%rax),%rdx
  mov 0x108(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_60
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_49:
  mov (%rbx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0x98(%rcx),%rcx
  inc %rsi
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_60:
  cmp %rdx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_49
  mov 0x128(%rax),%rdx
  mov 0x120(%rax),%rbx
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_8d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_77:
  mov (%rbx,%rax,8),%rsi
  mov 0x10(%rsi),%rsi
  lea (%rcx,%rsi,1),%rcx
  lea 0x98(%rcx),%rcx
  inc %rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_8d:
  cmp %rdx,%rax
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_77
  mov %rcx,%rax
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
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit.SizeSSZ:
  mov $0x4d8,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Deposit_Data.SizeSSZ:
  mov $0xb8,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DepositMessage.SizeSSZ:
  mov $0x58,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ENRForkID.SizeSSZ:
  mov $0x10,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Eth1Data.SizeSSZ:
  mov $0x48,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Fork.SizeSSZ:
  mov $0x10,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ForkData.SizeSSZ:
  mov $0x24,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.HistoricalBatch.SizeSSZ:
  mov $0x80000,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.IndexedAttestation.SizeSSZ:
  mov 0x10(%rax),%rax
  shl $0x3,%rax
  add $0xe4,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PendingAttestation.SizeSSZ:
  mov 0x10(%rax),%rax
  add $0x94,%rax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.PowBlock.SizeSSZ:
  mov $0x60,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ProposerSlashing.SizeSSZ:
  mov $0x1a0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_b0
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1373632(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x10(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1368512(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_98:
  mov %rax,0x10(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_9c:
  mov 0x10(%rcx),%rcx
  mov 0x10(%rcx),%rax
  add $0x1b4,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_b0:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedAggregateAttestationAndProof.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_b1
  push %rbp
  mov %rsp,%rbp
  sub $0x18,%rsp
  cmpq $0x0,0x8(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_56
  mov %rax,0x28(%rsp)
  lea type__+1468832(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_3a
  mov 0x28(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_4f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_3a:
  mov 0x28(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_4f:
  mov %rax,0x8(%rcx)
  mov %rcx,%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_56:
  mov 0x8(%rax),%rcx
  cmpq $0x0,0x48(%rcx)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_9c
  mov %rcx,0x10(%rsp)
  lea type__+1576736(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_83
  mov 0x10(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_98
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_83:
  mov 0x10(%rsp),%rcx
  mov 0x48(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_98:
  mov %rax,0x48(%rcx)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_9c:
  mov 0x48(%rcx),%rax
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBody.SizeSSZ
  add $0xb8,%rax
  add $0x18,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_b1:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlock.SizeSSZ_0
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedBeaconBlockHeader.SizeSSZ:
  mov $0xd0,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SignedVoluntaryExit.SizeSSZ:
  mov $0x70,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SigningData.SizeSSZ:
  mov $0x40,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Status.SizeSSZ:
  mov $0x54,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Validator.SizeSSZ:
  mov $0x79,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.ValidatorBalance.SizeSSZ:
  mov $0x10,%eax
  retq
github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.VoluntaryExit.SizeSSZ:
  mov $0x10,%eax
  retq
