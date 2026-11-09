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
