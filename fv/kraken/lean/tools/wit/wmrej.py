import sys,subprocess; sys.path.insert(0,sys.argv[1]); import wgen
# Witnesses of the marshal reject theorems (re-proof R6): ListU64 (> 16
# elements), FixedVec (len(W) != 4), Checkpoint (len(Root) != 32). The error
# global at data label 0 (0x10000).
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
ZB="Int.toBytes 8 (0 : BitVec 64).toInt"
MODE=sys.argv[2]
def addrs(ch):
    a=65536; ad={}
    for k,e,n in ch: ad[k]=a; a+=n
    return ad
def post(src, lab):
    src=src.replace('[.label "runtime.writeBarrier",',f'[.label "{lab}",',1)
    src=src.replace("abbrev z (k : Nat) : List UInt8 := List.replicate k 0",f"""set_option maxRecDepth 100000 in
theorem label_err : label "{lab}" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

abbrev z (k : Nat) : List UInt8 := List.replicate k 0""",1)
    src=src.replace("  simp only [s, s0, UInt64.toBitVec_ofNat,","  rw [label_err]\n  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat, BitVec.reduceAdd]\n  simp only [s, s0, UInt64.toBitVec_ofNat,",1)
    src=src.replace("  apply sep_true (F := )\n","  apply sep_true (F := Std.ExtHashMap.emp)\n  simp only [Std.ExtHashMap.sep_emp]\n",1)
    src=src.replace("  first | (refine Eq.mp ?_ H; exact congrFun (by ac_rfl) _) | ecancel","  refine Eq.mp ?_ H\n  exact congrFun (by ac_rfl) _",1)
    src=src.replace("set_option maxHeartbeats 4000000 in\nset_option maxRecDepth 100000 in\ntheorem s_mem","set_option maxHeartbeats 32000000 in\nset_option maxRecDepth 100000 in\ntheorem s_mem",1)
    return src
MEM="(by have h := s_mem zmms flags; simp only [Std.ExtHashMap.sep_assoc] at h ⊢; exact h)"
if MODE=="lu":
    lab="ssz.ErrListTooBig"
    ch=[("e0",ZB,8),("e1",ZB,8),("guard",Z,8),("l1","z 8",8),("l2","z 8",8),("fp","z 8",8),("ra",Z,8),("hole","z 8",8),("slot","z 8",8),
        ("pp",ZB,8),("nn","Int.toBytes 8 (17 : Int)",8),("o4","z 4",4)]
    R="Eq ((z 8).At (s.regs.rsp.toBitVec + 8))"
    prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (({ZB}).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (17 : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (([] : List UInt8).At s.regs.rbx.toBitVec) ⋆ Eq ((z 4).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (({ZB}).At (label "{lab}").toBitVec) ⋆ Eq (({ZB}).At (label "{lab}" + 8).toBitVec) ⋆ {R}"""
    tgt,tlen,mods,ns,thm="ListU64MarshalSSZTo",91,[],"WitLuMR","lu_marshal_reject_main"
    regs=lambda a: f"{hex(a['pp'])}, {hex(a['o4'])}, 0, 0, 0, 4, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"[] (z 4) 17 (by decide) (by decide) rfl 0 0 0 (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ fun _ => True) {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])"
    imports=["import Fk.LuMarshal"]
if MODE=="fv":
    lab="ssz.ErrBytesLength"
    ch=[("e0",ZB,8),("e1",ZB,8),("guard",Z,8),("rslot","z 8",8),("hole1","z 72",72),("l4","z 8",8),("l3","z 8",8),("l2","z 8",8),("l1","z 8",8),
        ("fp","z 8",8),("ra",Z,8),("s1","z 8",8),("s2","z 8",8),("r0","z 1",1),("r1","z 31",31),("wp",ZB,8),("wl",ZB,8),("d0","z 32",32)]
    R="Eq ((z 72).At (s.regs.rsp.toBitVec - 112))"
    prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((z 1).At s.regs.rax.toBitVec) ⋆ Eq ((z 31).At (s.regs.rax.toBitVec + 1))
      ⋆ Eq (({ZB}).At (s.regs.rax.toBitVec + 32)) ⋆ Eq (({ZB}).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq (([] : List UInt8).At s.regs.rbx.toBitVec) ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (({ZB}).At (label "{lab}").toBitVec) ⋆ Eq (({ZB}).At (label "{lab}" + 8).toBitVec) ⋆ {R}"""
    tgt,tlen,mods,ns,thm="FixedVecMarshalSSZTo",99,[("rtcopy","RtCopy",26)],"WitFvMR","fv_marshal_reject_main"
    regs=lambda a: f"{hex(a['r0'])}, {hex(a['d0'])}, 0, 0, 0, 64, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"(z 32) [] (z 32) rfl rfl 0 0 0 0 (by decide) (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 1) (z 31) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ fun _ => True) 0 [] rfl {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) (rt_memmove RTC hk_rtcopy hf_rtcopy 0)"
    imports=["import Fk.FvMarshal"]
if MODE=="cp":
    lab="ssz.ErrBytesLength"
    ch=[("e0",Z,8),("e1",Z,8),("guard",Z,8),("rslot","z 8",8),("hole1","z 72",72),("l40","z 8",8),("l32","z 8",8),("hole2","z 8",8),("l16","z 8",8),
        ("fp","z 8",8),("ra",Z,8),("hole3","z 8",8),("s2","z 8",8),("e8","z 8",8),("pp",ZB,8),("nn",ZB,8),("root","z 32",32),("d0","z 8",8),("d1","z 32",32)]
    ad=addrs(ch); P=hex(ad["root"])
    ch=[(k,(f"Int.toBytes 8 ({P} : BitVec 64).toInt" if k=="pp" else e),n) for k,e,n in ch]
    R="Eq ((z 72).At (s.regs.rsp.toBitVec - 112)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))"
    prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 ({P} : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (({ZB}).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((z 32).At ({P} : BitVec 64))
      ⋆ Eq (({Z}).At (label "{lab}").toBitVec) ⋆ Eq (({Z}).At (label "{lab}" + 8).toBitVec)
      ⋆ Eq (([] : List UInt8).At s.regs.rbx.toBitVec) ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ {R}"""
    tgt,tlen,mods,ns,thm="PrysmCheckpointMarshalSSZTo",82,[("rtcopy","RtCopy",26)],"WitCpMR","cp_marshal_reject_main"
    regs=lambda a: f"{hex(a['e8'])}, {hex(a['d0'])}, 0, 0, 0, 40, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"(z 8) (z 32) [] (z 8) (z 32) rfl rfl rfl rfl ({P} : BitVec 64) 0 (by decide) 0 0 (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ fun _ => True) 0 [] rfl {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) (rt_memmove RTC hk_rtcopy hf_rtcopy 0)"
    imports=["import Fk.CpMarshal"]
cfg=dict(ns=ns,imports=imports,doc=f"""# Premise witness of `{thm}` (re-proof R6)

Host: data label 0 renamed to `{lab}` (the error global at 0x10000) and the
real encoder (index 5){', RtCopy' if mods else ''}. Generated by `tools/wit/wmrej.py {MODE}`.""",
 target=tgt,tlen=tlen,models=mods,chunks=ch,pbinders="",pnames="",lenhyps="",lenhypnames=[],
 regs=regs,premise=prem,
 main=lambda st: f"""/-- **Non-vacuity of `{thm}`.** The encoder returns the error global. -/
theorem {thm.replace('_main','_runs')} (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0)
      ⟨s0 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono ({thm} 5 hk_target hf_target {args.replace('RTC', str(st.get('rtcopy',0)))})
    (fun _ h => ⟨h.1, h.2.1⟩)
""")
src,addr,starts=wgen.gen2(cfg)
open(f"Fk/{ns}.lean","w").write(post(src,lab)); print(ns)
