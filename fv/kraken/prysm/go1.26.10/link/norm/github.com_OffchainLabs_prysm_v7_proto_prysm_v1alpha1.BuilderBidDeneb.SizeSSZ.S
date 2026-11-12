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
