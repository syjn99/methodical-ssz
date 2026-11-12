runtime.memmove:
  mov %rax,%rdi
  mov %rbx,%rsi
  mov %rcx,%rdx
  jmp L_fvcopy
runtime.growslice:
  mov %rbx,%rdx
  sub %rdi,%rdx
  mov %rax,%rsi
  mov runtime.fvBump(%rip),%rdi
  lea 0xc0(%rbx,%rbx,1),%rcx
  lea (%rdi,%rcx,1),%r8
  mov %r8,runtime.fvBump(%rip)
  mov %rdi,%rax
  jmp L_fvcopy
L_fvcopy:
  mov $0x0,%r10
L_fvcopy_loop:
  cmp %rdx,%r10
  je L_fvcopy_done
  movzbl (%rsi,%r10,1),%r11d
  mov %r11b,(%rdi,%r10,1)
  add $0x1,%r10
  jmp L_fvcopy_loop
L_fvcopy_done:
  retq
