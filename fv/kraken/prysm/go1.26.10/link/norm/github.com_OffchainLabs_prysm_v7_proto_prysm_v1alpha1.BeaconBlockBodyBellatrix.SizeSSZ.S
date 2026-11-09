github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_22f
  push %rbp
  mov %rsp,%rbp
  sub $0x40,%rsp
  mov %rax,0x50(%rsp)
  mov 0x48(%rax),%rcx
  imul $0x1a0,%rcx,%rcx
  add $0x180,%rcx
  mov 0x60(%rax),%rdx
  mov %rdx,0x28(%rsp)
  mov 0x58(%rax),%rbx
  mov %rbx,0x38(%rsp)
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_55
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f:
  mov 0x10(%rdi),%rdi
  add 0x10(%rdi),%r8
  lea (%rcx,%r8,8),%rcx
  lea 0x1d4(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_55:
  cmp %rdx,%rsi
  jge L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_148
  mov %rsi,0x20(%rsp)
  mov %rcx,0x10(%rsp)
  mov (%rbx,%rsi,8),%rdi
  mov %rdi,0x30(%rsp)
  cmpq $0x0,0x8(%rdi)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ce
  lea type__+1368256(%rip),%rax
  nop
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_95
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ac
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_95:
  mov 0x30(%rsp),%rcx
  mov 0x8(%rcx),%rdx
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ac:
  mov %rax,0x8(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x10(%rsp),%rcx
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov 0x30(%rsp),%rdi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_ce:
  mov 0x8(%rdi),%r8
  mov 0x10(%r8),%r8
  cmpq $0x0,0x10(%rdi)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f
  mov %r8,0x18(%rsp)
  lea type__+1368256(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  nop
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_109
  mov 0x30(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_11e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_109:
  mov 0x30(%rsp),%rcx
  mov 0x10(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_11e:
  mov %rax,0x10(%rcx)
  mov 0x50(%rsp),%rax
  mov 0x28(%rsp),%rdx
  mov 0x38(%rsp),%rbx
  mov 0x20(%rsp),%rsi
  mov %rcx,%rdi
  mov 0x18(%rsp),%r8
  mov 0x10(%rsp),%rcx
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_3f
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_148:
  mov 0x70(%rax),%rdx
  mov 0x78(%rax),%rbx
  xor %esi,%esi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_16a
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_154:
  mov (%rdx,%rsi,8),%rdi
  mov 0x10(%rdi),%rdi
  lea (%rcx,%rdi,1),%rcx
  lea 0xe8(%rcx),%rcx
  inc %rsi
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_16a:
  cmp %rbx,%rsi
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_154
  mov 0x90(%rax),%rdx
  imul $0x4d8,%rdx,%rdx
  add %rdx,%rcx
  mov 0xa8(%rax),%rdx
  imul $0x70,%rdx,%rdx
  add %rdx,%rcx
  cmpq $0x0,0xc0(%rax)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1e0
  mov %rcx,0x10(%rsp)
  lea type__+1660384(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1b9
  mov 0x50(%rsp),%rcx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1d1
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1b9:
  mov 0x50(%rsp),%rcx
  mov 0xc0(%rcx),%rdx
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rdx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1d1:
  mov %rax,0xc0(%rcx)
  mov %rcx,%rax
  mov 0x10(%rsp),%rcx
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_1e0:
  mov 0xc0(%rax),%rdx
  mov 0xc0(%rdx),%rbx
  mov 0x100(%rdx),%rsi
  add $0x1fc,%rbx
  mov 0x108(%rdx),%rdx
  xor %eax,%eax
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_220
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_207:
  mov %rsi,%rdi
  mov 0x8(%rdi),%rdi
  lea (%rbx,%rdi,1),%rbx
  lea 0x4(%rbx),%rbx
  add $0x18,%rsi
  inc %rax
  nop
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_220:
  cmp %rdx,%rax
  jl L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_207
  lea (%rcx,%rbx,1),%rax
  add $0x40,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_22f:
  mov %rax,0x8(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  nop
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.BeaconBlockBodyBellatrix.SizeSSZ_0
