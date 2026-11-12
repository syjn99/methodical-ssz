github.com_OffchainLabs_prysm_v7_proto_engine_v1.ExecutionRequests.SizeSSZ:
  mov 0x10(%rax),%rcx
  lea (%rcx,%rcx,2),%rcx
  shl $0x6,%rcx
  mov 0x28(%rax),%rdx
  imul $0x4c,%rdx,%rdx
  add %rdx,%rcx
  mov 0x40(%rax),%rdx
  imul $0x74,%rdx,%rdx
  lea (%rcx,%rdx,1),%rax
  lea 0xc(%rax),%rax
  retq
