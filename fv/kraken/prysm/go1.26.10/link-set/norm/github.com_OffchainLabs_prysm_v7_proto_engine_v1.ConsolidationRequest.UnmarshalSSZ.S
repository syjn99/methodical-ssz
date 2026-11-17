github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_224
  push %rbp
  mov %rsp,%rbp
  sub $0x20,%rsp
  mov %rbx,0x38(%rsp)
  nop
  cmp $0x74,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_210
  mov %rax,0x30(%rsp)
  mov %rbx,0x38(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x14,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_75
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_75:
  mov %rax,0x18(%rsp)
  mov %rax,0x8(%rdx)
  mov 0x38(%rsp),%rbx
  mov $0x14,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x14,0x10(%rdx)
  movq $0x14,0x18(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_b2
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_c7
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_b2:
  mov 0x8(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_c7:
  mov %rdi,0x8(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_10c
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_10c:
  mov %rax,0x18(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x14,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x28(%rdx)
  movq $0x30,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_14d
  mov 0x18(%rsp),%rdi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_162
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_14d:
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rdi
  mov %rdi,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_162:
  mov %rdi,0x20(%rdx)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x30,%ecx
  callq runtime.makeslice
  mov 0x30(%rsp),%rdx
  movq $0x0,0x40(%rdx)
  movq $0x30,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ac
  mov 0x38(%rdx),%rsi
  nop
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ac:
  mov %rax,0x18(%rsp)
  mov %rax,0x38(%rdx)
  mov 0x38(%rsp),%rbx
  add $0x44,%rbx
  mov $0x30,%ecx
  callq runtime.memmove
  mov 0x30(%rsp),%rdx
  movq $0x30,0x40(%rdx)
  movq $0x30,0x48(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ed
  mov 0x18(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_202
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_1ed:
  mov 0x38(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x18(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_202:
  mov %rsi,0x38(%rdx)
  xor %eax,%eax
  xor %ebx,%ebx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_210:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x20,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_224:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_engine_v1.ConsolidationRequest.UnmarshalSSZ_0
