runtime.newobject:
  lea type__+1464512(%rip),%rsi
  cmp %rsi,%rax
  je L_lvNewT3_96
  mov runtime.fvBump(%rip),%rdx
  lea 0x48(%rdx),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
L_lvNewT3_96:
  mov runtime.fvBump(%rip),%rdx
  lea 0x60(%rdx),%rsi
  mov %rsi,runtime.fvBump(%rip)
  mov %rdx,%rax
  retq
