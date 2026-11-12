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
