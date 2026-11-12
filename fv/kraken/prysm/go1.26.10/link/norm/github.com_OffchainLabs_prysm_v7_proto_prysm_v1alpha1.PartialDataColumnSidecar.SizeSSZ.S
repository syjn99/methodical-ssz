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
