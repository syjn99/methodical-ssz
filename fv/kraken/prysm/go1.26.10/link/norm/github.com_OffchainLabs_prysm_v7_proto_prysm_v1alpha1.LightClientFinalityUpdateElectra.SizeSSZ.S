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
