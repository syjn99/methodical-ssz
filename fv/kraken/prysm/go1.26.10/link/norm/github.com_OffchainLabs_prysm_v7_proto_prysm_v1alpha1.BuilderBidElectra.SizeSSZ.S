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
