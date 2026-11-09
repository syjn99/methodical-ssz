import sys,subprocess; sys.path.insert(0,sys.argv[1]); import wgen
# Witnesses of the marshal reject theorems (re-proof R6): ListU64 (> 16
# elements), FixedVec (len(W) != 4), Checkpoint (len(Root) != 32). The error
# global at data label 0 (0x10000), initialized as Go's errors.New leaves it
# (fix 3 X3): the errorString itab at data label 1, a pointer to a 16-byte
# errorString with the message "err".
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
ZB="Int.toBytes 8 (0 : BitVec 64).toInt"
MODE=sys.argv[2]
ITAB=0x10001
E0=f"Int.toBytes 8 ({ITAB}#64).toInt"; E1="Int.toBytes 8 (OBJ#64).toInt"
G0=f"Int.toBytes 8 ({ITAB} : BitVec 64).toInt"
def errobj(ch):
    ch=[(k,(E0 if k=="e0" else E1 if k=="e1" else e),n) for k,e,n in ch]
    ch=wgen.aligned(ch+[("eo_sp","SPV",8)],{"eo_sp"})[:-1]
    obj=65536+sum(n for _,_,n in ch); sp=obj+16
    ch+=[("eo_sp",f"Int.toBytes 8 ({sp}#64).toInt",8),("eo_len","Int.toBytes 8 (BitVec.ofNat 64 3).toInt",8),("emsg","[101, 114, 114]",3)]
    ch=[(k,e.replace("OBJ#64",f"{obj}#64"),n) for k,e,n in ch]
    err=f"""((Eq ((Int.toBytes 8 ({sp} : BitVec 64).toInt).At ({obj} : UInt64).toBitVec)
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({obj} : UInt64).toBitVec + 8)))
        ⋆ Eq ([101, 114, 114].At ({sp} : BitVec 64)))"""
    return ch, obj, sp, err
addrs=wgen.addrs
def post(src, lab):
    src=wgen.sub(src,'[.label "runtime.writeBarrier",',f'[.label "{lab}",',1)
    src=wgen.sub(src,'.label "pad1"','.label "go_itab._errors.errorString_error"',1)
    src=wgen.sub(src,"abbrev z (k : Nat) : List UInt8 := List.replicate k 0",f"""set_option maxRecDepth 100000 in
theorem label_err : label "{lab}" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

theorem errstr_eq : ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114]
    = (Eq ((Int.toBytes 8 ({SP} : BitVec 64).toInt).At ({OBJ} : UInt64).toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({OBJ} : UInt64).toBitVec + 8)))
      ⋆ Eq ([101, 114, 114].At ({SP} : BitVec 64)) := by
  unfold ErrStr ErrObj
  rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
  rfl

abbrev z (k : Nat) : List UInt8 := List.replicate k 0""",1)
    src=wgen.sub(src,"  simp only [s, s0, UInt64.toBitVec_ofNat,","  rw [label_err]\n  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat, BitVec.reduceAdd]\n  simp only [s, s0, UInt64.toBitVec_ofNat,",1)
    src=wgen.post_ac(src)
    return src
MEM="(by rw [errstr_eq]; have h := s_mem zmms flags; simp only [Std.ExtHashMap.sep_assoc] at h ⊢; exact h)"
if MODE=="lu":
    lab="ssz.ErrListTooBig"
    ch=[("e0",ZB,8),("e1",ZB,8),("guard",Z,8),("l1","z 8",8),("l2","z 8",8),("fp","z 8",8),("ra",Z,8),("hole","z 8",8),("slot","z 8",8),
        ("pp","Int.toBytes 8 (PP : BitVec 64).toInt",8),("nn","Int.toBytes 8 (17 : Int)",8),("gap_lc","Int.toBytes 8 (17 : Int)",8),
        ("o4","z 4",4),("gap_ld","z 136",136)]
    ch=wgen.aligned(ch,{"gap_ld"})  # the []uint64 data 8-aligned (fix 2 X3)
    ad=addrs(ch); PP=hex(ad["gap_ld"])
    ch=[(k,e.replace("PP :",PP+" :"),n) for k,e,n in ch]
    ch,OBJ,SP,ERR=errobj(ch)
    R="Eq ((z 8).At (s.regs.rsp.toBitVec + 8))"
    prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 ({PP} : BitVec 64).toInt).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 (17 : Int)).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (([] : List UInt8).At s.regs.rbx.toBitVec) ⋆ Eq ((z 4).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq (({G0}).At (label "{lab}").toBitVec) ⋆ Eq ((Int.toBytes 8 ({OBJ} : BitVec 64).toInt).At (label "{lab}" + 8).toBitVec) ⋆ {R} ⋆ {ERR}"""
    tgt,tlen,mods,ns,thm="ListU64MarshalSSZTo",91,[],"WitLuMR","lu_marshal_reject_main"
    regs=lambda a: f"{hex(a['pp'])}, {hex(a['o4'])}, 0, 0, 0, 4, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"[] (z 4) 17 (by decide) (by decide) rfl ({PP} : BitVec 64) {ITAB} {OBJ} (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114] ⋆ fun _ => True) {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])"
    imports=["import Fk.LuMarshal"]
if MODE=="fv":
    lab="ssz.ErrBytesLength"
    ch=[("e0",ZB,8),("e1",ZB,8),("guard",Z,8),("rslot","z 8",8),("hole1","z 72",72),("l4","z 8",8),("l3","z 8",8),("l2","z 8",8),("l1","z 8",8),
        ("fp","z 8",8),("ra",Z,8),("s1","z 8",8),("s2","z 8",8),("r0","z 1",1),("r1","z 31",31),("wp",ZB,8),("wl",ZB,8),("gap_wc",ZB,8),("d0","z 32",32),("gap_d1","z 32",32)]
    ch,OBJ,SP,ERR=errobj(ch)
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
      ⋆ Eq (({G0}).At (label "{lab}").toBitVec) ⋆ Eq ((Int.toBytes 8 ({OBJ} : BitVec 64).toInt).At (label "{lab}" + 8).toBitVec) ⋆ {R} ⋆ {ERR}"""
    tgt,tlen,mods,ns,thm="FixedVecMarshalSSZTo",99,[("rtcopy","RtCopy",26)],"WitFvMR","fv_marshal_reject_main"
    regs=lambda a: f"{hex(a['r0'])}, {hex(a['d0'])}, 0, 0, 0, 64, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"(z 32) [] (z 32) rfl rfl 0 0 {ITAB} {OBJ} (by decide) (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 1) (z 31) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114] ⋆ fun _ => True) 0 [] rfl {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) (rt_memmove RTC hk_rtcopy hf_rtcopy 0)"
    imports=["import Fk.FvMarshal"]
if MODE=="cp":
    lab="ssz.ErrBytesLength"
    ch=[("e0",Z,8),("e1",Z,8),("guard",Z,8),("rslot","z 8",8),("hole1","z 72",72),("l40","z 8",8),("l32","z 8",8),("hole2","z 8",8),("l16","z 8",8),
        ("fp","z 8",8),("ra",Z,8),("hole3","z 8",8),("s2","z 8",8),("e8","z 8",8),("pp",ZB,8),("nn",ZB,8),("gap_rc",ZB,8),("root","z 32",32),("d0","z 8",8),("d1","z 32",32)]
    ad=addrs(ch); P=hex(ad["root"])
    ch=[(k,(f"Int.toBytes 8 ({P} : BitVec 64).toInt" if k=="pp" else e),n) for k,e,n in ch]
    ch,OBJ,SP,ERR=errobj(ch)
    R="Eq ((z 72).At (s.regs.rsp.toBitVec - 112)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 24)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))"
    prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((Int.toBytes 8 ({P} : BitVec 64).toInt).At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (({ZB}).At (s.regs.rax.toBitVec + 16)) ⋆ Eq ((z 32).At ({P} : BitVec 64))
      ⋆ Eq ((Int.toBytes 8 ({ITAB} : UInt64).toBitVec.toInt).At (label "{lab}").toBitVec) ⋆ Eq ((Int.toBytes 8 ({OBJ} : UInt64).toBitVec.toInt).At (label "{lab}" + 8).toBitVec)
      ⋆ Eq (([] : List UInt8).At s.regs.rbx.toBitVec) ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8)) ⋆ {R} ⋆ {ERR}"""
    tgt,tlen,mods,ns,thm="PrysmCheckpointMarshalSSZTo",82,[("rtcopy","RtCopy",26)],"WitCpMR","cp_marshal_reject_main"
    regs=lambda a: f"{hex(a['e8'])}, {hex(a['d0'])}, 0, 0, 0, 40, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0"
    args=f"(z 8) (z 32) [] (z 8) (z 32) rfl rfl rfl rfl ({P} : BitVec 64) 0 (by decide) {ITAB} {OBJ} (s0 zmms flags) 0 0 (by simp [s0]) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl ({R.replace('s.regs','(s0 zmms flags).regs')} ⋆ ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114] ⋆ fun _ => True) 0 [] rfl {MEM} (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) (rt_memmove RTC hk_rtcopy hf_rtcopy 0)"
    imports=["import Fk.CpMarshal"]
cfg=dict(ns=ns,imports=imports+["import Fk.Contracts"],doc=f"""# Premise witness of `{thm}` (re-proof R6)

Host: data label 0 renamed to `{lab}` (the error global at 0x10000), data
label 1 to the errorString itab, and the real encoder (index 5){', RtCopy' if mods else ''}.
The global is initialized: (itab, e1), e1 a 16-byte errorString with the
message "err". Generated by `tools/wit/wmrej.py {MODE}`.""",
 target=tgt,tlen=tlen,models=mods,chunks=ch,pbinders="",pnames="",lenhyps="",lenhypnames=[],
 regs=regs,premise=prem,
 main=lambda st: f"""/-- **Non-vacuity of `{thm}`.** The encoder returns a nil slice and the
initialized error global: a non-nil error (rdi). -/
theorem {thm.replace('_main','_runs')} (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rdi ≠ 0)
      ⟨s0 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono ({thm} 5 hk_target hf_target {args.replace('RTC', str(st.get('rtcopy',0)))})
    (fun _ h => ⟨h.1, h.2.1, fun h0 => absurd (h0 ▸ h.2.2.2.2.1) (by decide)⟩)
""")
src,addr,starts=wgen.gen2(cfg)
wgen.write(f"Fk/{ns}.lean", post(src,lab)); print(ns)
