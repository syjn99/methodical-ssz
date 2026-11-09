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
