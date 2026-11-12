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
