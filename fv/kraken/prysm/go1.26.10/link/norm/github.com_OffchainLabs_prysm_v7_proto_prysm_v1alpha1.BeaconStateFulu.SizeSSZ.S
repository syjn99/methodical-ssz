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
