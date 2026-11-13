github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_233
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0xb8,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_21f
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_78
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_78:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x10(%rdx)
  movq $0x30,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_b5
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_ca
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_b5:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_ca:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x20,%ecx
  nop
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_113
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_113:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x30,%rbx
  mov $0x20,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x20,0x28(%rdx)
  movq $0x20,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_154
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_169
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_154:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_169:
  mov %rdi,0x20(%rdx)
  mov 0x38(%rsp),%rsi
  mov 0x50(%rsi),%rsi
  mov %rsi,0x38(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1bb
  mov 0x40(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1bb:
  mov %rax,0x18(%rsp)
  mov %rax,0x40(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x58,%rbx
  mov $0x60,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x60,0x48(%rdx)
  movq $0x60,0x50(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1fc
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_211
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_1fc:
  mov 0x40(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_211:
  mov %rsi,0x40(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_21f:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_233:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.BuilderDepositRequest.UnmarshalSSZ_0
