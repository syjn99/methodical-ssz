import sys; sys.path.insert(0,sys.argv[1]); import wgen
N=int(sys.argv[2])  # elements of L: 0, 1, 16
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
ch=[("guard",Z,8),("blk","z 144",144),("rslot","z 8",8),("cspill","z 16",16),("gap1","z 24",24),("l56","z 8",8),("l48","z 8",8),
    ("gap2","z 32",32),("fp","z 8",8),("ra",Z,8),("x8","z 8",8),("x16","z 8",8),("x24","z 8",8),("x32","z 8",8),
    ("cA","z 8",8),("cS","z 8",8),("cL","z 8",8),
    ("a8","a8",8),("f0","f0",1),("f1","f1",2),("f2","f2",4),("f3","f3",8),("f4","f4",1),
    ("o28","[28, 0, 0, 0]",4),("o4","[4, 0, 0, 0]",4),("lb","lb",8*N)]
prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 24))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 32)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 56))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 48)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 104))
      ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq ((z 144).At (s.regs.rsp.toBitVec - 104 - 144 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16)) ⋆ bumpHeap 176
      ⋆ Eq (a8.At s.regs.rbx.toBitVec)
      ⋆ Eq (f0.At (s.regs.rbx.toBitVec + 8)) ⋆ Eq (f1.At (s.regs.rbx.toBitVec + 8 + 1))
      ⋆ Eq (f2.At (s.regs.rbx.toBitVec + 8 + 3)) ⋆ Eq (f3.At (s.regs.rbx.toBitVec + 8 + 7))
      ⋆ Eq (f4.At (s.regs.rbx.toBitVec + 8 + 15))
      ⋆ Eq ([28, 0, 0, 0].At (s.regs.rbx.toBitVec + 24))
      ⋆ Eq ([4, 0, 0, 0].At (s.regs.rbx.toBitVec + 28)) ⋆ Eq (lb.At (s.regs.rbx.toBitVec + 28 + 4))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)"""
cfg=dict(ns=f"WitNe{N}",opens=" Fv1",imports=["import Fk.NeAccept","import Fk.BumpMore"],
 doc=f"""# Premise witness of `ne_accept_main` (1b-fix X4)

Host: data labels, the real Nested.UnmarshalSSZ (index 5), Scalars.UnmarshalSSZ
and ListU64.UnmarshalSSZ (the callees), the bump `runtime.makeslice`
(8-byte elements) and the 24-byte bump `runtime.newobject`. The two function
specifications are not assumed: `ScUAccC` comes from `sc_uacc_holds` and
`LuUAccC` from `lu_uacc_holds` (with `bump_makeslice`) on the callee code in
the same host. For every A word, Scalars value and ListU64 value with at most
16 elements, `s0` meets every premise of `ne_accept_main` and the function
returns nil. This file: L with {N} elements (`WitNe0`, `WitNe1`, `WitNe16` cover empty, one, maximum).""",
 target="NestedUnmarshalSSZ",tlen=157,
 models=[("fnSc","ScalarsUnmarshalSSZ",33),("fnLu","ListU64UnmarshalSSZ",193),("makeslice","BumpAlloc",6),("newobject","BumpNew24",6)],
 chunks=ch,heap=176,
 pbinders="(a8 f0 f1 f2 f3 f4 lb : List UInt8)",pnames="a8 f0 f1 f2 f3 f4 lb",
 lenhyps=f"(ha8 : a8.length = 8) (h0 : f0.length = 1) (h1 : f1.length = 2) (h2 : f2.length = 4) (h3 : f3.length = 8) (h4 : f4.length = 1) (hlb : lb.length = {8*N})",lenhypnames=["ha8","h0","h1","h2","h3","h4","hlb"],
 
 regs=lambda a: f"{hex(a['cA'])}, {hex(a['a8'])}, {32+8*N}, 0, 0, {32+8*N}, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0",
 premise=prem,
 main=lambda st: f"""/-- **Non-vacuity of `ne_accept_main`.** Every premise holds in this host: the
two `newobject` contracts by `bump_newobject24`, `ScUAccC` by `sc_uacc_holds`
and `LuUAccC` by `lu_uacc_holds` (callee code in the same host, its makeslice
by `bump_makeslice`). The function returns nil. -/
theorem ne_accept_runs (a8 : List UInt8) (sg : Scalars) (lg : ListU64) (ha8 : a8.length = 8)
    (hlen : lg.l.length = {N}) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0)
      ⟨s0 a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
        zmms flags, Host.addrOf 5⟩ := by
  have hlg : lg.ok := by simp [ListU64.ok, hlen]
  exact eventually_mono (ne_accept_main 5 hk_target hf_target a8 ha8 sg lg hlg
    (s0 a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
      zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 16) (z 144) (z 8) (z 8) (z 8)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 (by decide) rfl rfl rfl rfl
    (fun _ => True) bumpHeap 176
    (s_mem a8 (scField sg 0) (scField sg 1) (scField sg 2) (scField sg 3) (scField sg 4) (u64Bytes lg.l).toList
      ha8 (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size])
      (by simp [scField, Fv.uintBytes_size]) (by simp [scField, Fv.uintBytes_size]) (by simp [scField])
      (by simp [u64Bytes_size, hlen]) zmms flags)
    (by simp [s0]) (by simp [s0]) (by simp [s0, hlen]) (by simp [s0]) (by simp [s0]) (by omega)
    (bump_newobject24 {st['newobject']} hk_newobject hf_newobject _) (bump_newobject24 {st['newobject']} hk_newobject hf_newobject _)
    (sc_uacc_holds {st['fnSc']} hk_fnSc hf_fnSc)
    (lu_uacc_holds {st['fnLu']} hk_fnLu hf_fnLu bumpHeap 0 (by decide) (bump_makeslice {st['makeslice']} hk_makeslice hf_makeslice _)))
    (fun _ h => ⟨h.1, h.2.1⟩)
""")
src,addr,st=wgen.gen(cfg)
wgen.write(f'Fk/WitNe{N}.lean', src)
print(st)
