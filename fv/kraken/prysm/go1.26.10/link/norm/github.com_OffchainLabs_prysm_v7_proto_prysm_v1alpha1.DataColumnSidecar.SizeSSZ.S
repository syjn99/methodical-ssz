github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.DataColumnSidecar.SizeSSZ:
  mov 0x18(%rax),%rcx
  shl $0xb,%rcx
  mov 0x30(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  add %rdx,%rcx
  mov 0x48(%rax),%rdx
  lea (%rdx,%rdx,2),%rdx
  shl $0x4,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0x164(%rax),%rax
  retq
