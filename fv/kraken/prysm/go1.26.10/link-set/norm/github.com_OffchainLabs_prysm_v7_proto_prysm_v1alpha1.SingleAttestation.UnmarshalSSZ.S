github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ:
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_0:
  cmp 0x10(%r14),%rsp
  jbe L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_30a
  push %rbp
  mov %rsp,%rbp
  sub $0x70,%rsp
  mov %rbx,0x88(%rsp)
  nop
  cmp $0xf0,%rcx
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2f6
  mov %rax,0x80(%rsp)
  mov %rdi,0x98(%rsp)
  mov %rbx,0x88(%rsp)
  test %al,(%rax)
  add $0x8,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.CommitteeIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_c7
  movups %xmm15,0x60(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_66
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_66:
  mov %rax,0x60(%rsp)
  mov %rbx,0x68(%rsp)
  lea go_string._+34185(%rip),%rax
  mov $0xf,%ebx
  lea 0x60(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_c1
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0xf,0x8(%rax)
  lea go_string._+34185(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_c1:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_c7:
  mov 0x88(%rsp),%rbx
  add $0x8,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x8,%rdi
  mov 0x80(%rsp),%rax
  add $0x10,%rax
  mov $0x8,%ecx
  callq github.com_OffchainLabs_prysm_v7_consensus_types_primitives.ValidatorIndex.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_167
  movups %xmm15,0x50(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_106
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_106:
  mov %rax,0x50(%rsp)
  mov %rbx,0x58(%rsp)
  lea go_string._+40288(%rip),%rax
  mov $0x11,%ebx
  lea 0x50(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_161
  nop
  lea type__+828672(%rip),%rax
  nop
  callq runtime.newobject
  movq $0x11,0x8(%rax)
  lea go_string._+40288(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_161:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_167:
  lea type__+1464512(%rip),%rax
  callq runtime.newobject
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_186
  mov 0x80(%rsp),%rdx
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_19e
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_186:
  mov 0x80(%rsp),%rdx
  mov 0x18(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_19e:
  mov %rax,0x18(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x10,%rbx
  mov 0x98(%rsp),%rdi
  add $-0x10,%rdi
  mov $0x80,%ecx
  nop
  callq github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.AttestationData.UnmarshalSSZ
  test %rax,%rax
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_234
  movups %xmm15,0x40(%rsp)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_1d6
  mov 0x8(%rax),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_1d6:
  mov %rax,0x40(%rsp)
  mov %rbx,0x48(%rsp)
  lea go_string._+15004(%rip),%rax
  mov $0x8,%ebx
  lea 0x40(%rsp),%rcx
  mov $0x1,%edi
  mov %rdi,%rsi
  callq fmt.errorf
  nop
  test %rax,%rax
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_22e
  nop
  lea type__+828672(%rip),%rax
  callq runtime.newobject
  movq $0x8,0x8(%rax)
  lea go_string._+15004(%rip),%rcx
  mov %rcx,(%rax)
  mov %rax,%rbx
  lea go_itab._errors.errorString_error(%rip),%rax
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_22e:
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_234:
  mov %rax,0x28(%rsp)
  mov %rbx,0x30(%rsp)
  lea type__+387072(%rip),%rax
  xor %ebx,%ebx
  mov $0x60,%ecx
  callq runtime.makeslice
  mov 0x80(%rsp),%rdx
  movq $0x0,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  je L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_282
  mov 0x20(%rdx),%rsi
  callq runtime.gcWriteBarrier2
  mov %rax,(%r11)
  mov %rsi,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_282:
  mov %rax,0x38(%rsp)
  mov %rax,0x20(%rdx)
  mov 0x88(%rsp),%rbx
  add $0x90,%rbx
  mov $0x60,%ecx
  nop
  callq runtime.memmove
  mov 0x80(%rsp),%rdx
  movq $0x60,0x28(%rdx)
  movq $0x60,0x30(%rdx)
  cmpl $0x0,runtime.writeBarrier(%rip)
  jne L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2cd
  mov 0x38(%rsp),%rsi
  jmp L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2e2
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2cd:
  mov 0x20(%rdx),%rcx
  callq runtime.gcWriteBarrier2
  mov 0x38(%rsp),%rsi
  mov %rsi,(%r11)
  mov %rcx,0x8(%r11)
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2e2:
  mov %rsi,0x20(%rdx)
  mov 0x28(%rsp),%rax
  mov 0x30(%rsp),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_2f6:
  mov ssz.ErrSize(%rip),%rax
  mov ssz.ErrSize+8(%rip),%rbx
  add $0x70,%rsp
  pop %rbp
  retq
L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_30a:
  mov %rax,0x8(%rsp)
  mov %rbx,0x10(%rsp)
  mov %rcx,0x18(%rsp)
  mov %rdi,0x20(%rsp)
  nop
  callq runtime.morestack_noctxt.abi0
  mov 0x8(%rsp),%rax
  mov 0x10(%rsp),%rbx
  mov 0x18(%rsp),%rcx
  mov 0x20(%rsp),%rdi
  jmpq L_github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.SingleAttestation.UnmarshalSSZ_0
