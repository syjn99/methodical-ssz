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
