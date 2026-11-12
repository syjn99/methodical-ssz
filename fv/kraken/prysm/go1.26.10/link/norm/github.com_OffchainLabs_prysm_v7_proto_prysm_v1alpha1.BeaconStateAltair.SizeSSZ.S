github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconStateAltair.SizeSSZ:
  mov 0x70(%rax),%rcx
  shl $0x5,%rcx
  mov 0x90(%rax),%rdx
  lea (%rdx,%rdx,8),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0xb0(%rax),%rdx
  imul $0x79,%rdx,%rdx
  add %rdx,%rcx
  mov 0xc8(%rax),%rdx
  lea (%rcx,%rdx,8),%rcx
  mov 0x110(%rax),%rdx
  add %rdx,%rcx
  mov 0x128(%rax),%rdx
  add %rdx,%rcx
  mov 0x170(%rax),%rdx
  lea (%rcx,%rdx,8),%rax
  lea 0x29c1f5(%rax),%rax
  retq
