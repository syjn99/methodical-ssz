github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ:
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
  lea 0x290191(%rcx),%rcx
  mov 0x110(%rax),%rdx
  mov 0x108(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_60
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_49:
  mov (%rbx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0x98(%rcx),%rcx
  inc %rsi
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_60:
  cmp %rdx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_49
  mov 0x128(%rax),%rdx
  mov 0x120(%rax),%rbx
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_8d
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_77:
  mov (%rbx,%rax,8),%rsi
  mov 0x10(%rsi),%rsi
  lea (%rcx,%rsi,1),%rcx
  lea 0x98(%rcx),%rcx
  inc %rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_8d:
  cmp %rdx,%rax
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconState.SizeSSZ_77
  mov %rcx,%rax
  retq
