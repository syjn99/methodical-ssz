import sys,subprocess; sys.path.insert(0,sys.argv[1]); import wgen
# Witnesses of the early-reject theorems (re-proof R6, fix 3 X3): the error
# global at data label 0 (0x10000), initialized as Go's errors.New leaves it
# (the errorString itab at data label 1, a pointer to a 16-byte errorString
# with the message "err"), the stack slots, an offset word if needed.
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
ITAB=0x10001
E0=f"Int.toBytes 8 ({ITAB}#64).toInt"; E1="Int.toBytes 8 (OBJ#64).toInt"
def errobj(ch):
    """Append the 8-aligned errorString object and its message; (ch, OBJ, SP, ERR)."""
    ch=wgen.aligned(ch+[("eo_sp","SPV",8)],{"eo_sp"})[:-1]
    obj=65536+sum(n for _,_,n in ch); sp=obj+16
    ch+=[("eo_sp",f"Int.toBytes 8 ({sp}#64).toInt",8),("eo_len","Int.toBytes 8 (BitVec.ofNat 64 3).toInt",8),("emsg","[101, 114, 114]",3)]
    ch=[(k,e.replace("OBJ#64",f"{obj}#64"),n) for k,e,n in ch]
    err=f"""((Eq ((Int.toBytes 8 ({sp} : BitVec 64).toInt).At ({obj} : UInt64).toBitVec)
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({obj} : UInt64).toBitVec + 8)))
        ⋆ Eq ([101, 114, 114].At ({sp} : BitVec 64)))"""
    return ch, obj, sp, err
ES="ssz.ErrSize"; EO="ssz.ErrInvalidVariableOffset"
# key, theorem, module, program, .S file, error label, kind, rcx, o4 offset from rbx, guard needs hsp
T=[("ScSz","sc_reject_size_main","ScReject","ScalarsUnmarshalSSZ","target.Scalars.UnmarshalSSZ",ES,"sc",0,None,False),
   ("FvSz","fv_reject_size_main","FvSmall","FixedVecUnmarshalSSZ","target.FixedVec.UnmarshalSSZ",ES,"size",0,None,False),
   ("BvSz","bv_reject_size_main","BvSpec","BitVecUnmarshalSSZ","target.BitVec.UnmarshalSSZ",ES,"size",0,None,False),
   ("CpSz","cp_reject_size_main","CpSpec","PrysmCheckpointUnmarshalSSZ","target_prysm.Checkpoint.UnmarshalSSZ",ES,"size",0,None,False),
   ("AdSz","ad_reject_size_main","AdSpec","PrysmAttestationDataUnmarshalSSZ","target_prysm.AttestationData.UnmarshalSSZ",ES,"size",0,None,False),
   ("LuSh","lu_reject_short_main","LuReject","ListU64UnmarshalSSZ","target.ListU64.UnmarshalSSZ",ES,"size",0,None,True),
   ("LuOf","lu_reject_offset_main","LuReject","ListU64UnmarshalSSZ","target.ListU64.UnmarshalSSZ",EO,"off",32,0,True),
   ("BlSh","bl_reject_short_main","BlSpec","BitLUnmarshalSSZ","target.BitL.UnmarshalSSZ",ES,"size",0,None,False),
   ("BlOf","bl_reject_offset_main","BlSpec","BitLUnmarshalSSZ","target.BitL.UnmarshalSSZ",EO,"off",32,0,False),
   ("NeSh","ne_reject_short_main","NeReject","NestedUnmarshalSSZ","target.Nested.UnmarshalSSZ",ES,"size",0,None,False),
   ("NeOf","ne_reject_offset_main","NeReject","NestedUnmarshalSSZ","target.Nested.UnmarshalSSZ",EO,"off",32,24,False),
   ("LcSh","lc_reject_short_main","LcReject","ListCUnmarshalSSZ","target.ListC.UnmarshalSSZ",ES,"size",0,None,False),
   ("LcOf","lc_reject_offset_main","LcReject","ListCUnmarshalSSZ","target.ListC.UnmarshalSSZ",EO,"off",32,0,False)]
only=sys.argv[2:] 
for key,thm,mod,prog,sfile,lab,kind,rcx,ooff,hsp in T:
    if only and key not in only: continue
    tlen=int(subprocess.check_output(["grep","-c","",f"../link/out/norm/{sfile}.S"]).strip())
    if kind=="sc":
        ch=[("e0",E0,8),("e1",E1,8),("ra",Z,8),("hole","z 8",8),("slot","z 8",8)]
        ch,OBJ,SP,ERR=errobj(ch)
        prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16#64))
      ⋆ Eq ((Int.toBytes 8 ({ITAB} : UInt64).toBitVec.toInt).At (label "{lab}").toBitVec) ⋆ Eq ((Int.toBytes 8 ({OBJ} : UInt64).toBitVec.toInt).At (label "{lab}" + 8).toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8)) ⋆ {ERR}"""
    else:
        ch=[("e0",E0,8),("e1",E1,8),("guard",Z,8),("fp","z 8",8),("ra",Z,8),("hole","z 8",8),("slot","z 8",8)]
        # Go values (re-proof fix X4): the 32 input bytes are all in the block.
        if kind=="off": ch+=([("gap_b0",f"z {ooff}",ooff)] if ooff else [])+[("o4","z 4",4),("gap_b1",f"z {32-4-ooff}",32-4-ooff)]
        ch,OBJ,SP,ERR=errobj(ch)
        o4a="" if kind!="off" else (f"\n      ⋆ Eq ((z 4).At s.regs.rbx.toBitVec)" if ooff==0 else f"\n      ⋆ Eq ((z 4).At (s.regs.rbx.toBitVec + {ooff}))")
        prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16)){o4a}
      ⋆ Eq ((Int.toBytes 8 ({ITAB} : UInt64).toBitVec.toInt).At (label "{lab}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({OBJ} : UInt64).toBitVec.toInt).At (label "{lab}" + 8).toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8)) ⋆ {ERR}"""
    R=f"Eq ((z 8).At ((s0 zmms flags).regs.rsp.toBitVec + 8)) ⋆ ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114] ⋆ fun _ => True"
    MEM="(by rw [errstr_eq]; have h := s_mem zmms flags; simp only [Std.ExtHashMap.sep_assoc] at h ⊢; exact h)"
    if kind=="sc":
        args=f"5 hk_target (fun i hi h => hf_target i hi _ h (by simp [{prog}])) (s0 zmms flags) 0 {ITAB} {OBJ} (z 8) rfl ({R}) {MEM} (by simp [s0])"
    else:
        o4args="" if kind!="off" else " (z 4) rfl (by decide)"
        g="(by simp [s0])"
        args=f"5 hk_target hf_target (s0 zmms flags) 0 0 {ITAB} {OBJ} (z 8) (z 8) rfl rfl{o4args} ({R}) {MEM} {g}"+(" (by simp [s0])" if hsp else "")+" (by simp [s0])"
    def regs(a, kind=kind, rcx=rcx, ooff=ooff):
        rbx = hex(a['o4']-(ooff or 0)) if kind=="off" else "0"
        r14 = hex(a['guard']-16) if kind!="sc" else "0"
        return f"0, {rbx}, {rcx}, 0, 0, {rcx}, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {r14}, 0"
    cfg=dict(ns=f"WitRj{key}",imports=[f"import Fk.{mod}","import Fk.Contracts"],doc=f"""# Premise witness of `{thm}` (re-proof R6)

Host: data label 0 renamed to `{lab}` (the error global at 0x10000), data
label 1 to the errorString itab, the real {sfile} (index 5). The global is
initialized: (itab, e1), e1 a 16-byte errorString with the message "err".
Generated by `tools/wit/wrej.py`.""",
      target=prog,tlen=tlen,models=[],chunks=ch,pbinders="",pnames="",lenhyps="",lenhypnames=[],
      regs=regs,premise=prem, main=lambda st,thm=thm,args=args: f"""/-- **Non-vacuity of `{thm}`.** The decoder returns the initialized error
global: a non-nil error. -/
theorem {thm.replace('_main','_runs')} (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨s0 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono ({thm} {args})
    (fun _ h => ⟨h.1, by rw [h.2.1]; decide⟩)
""")
    src,addr,starts=wgen.gen2(cfg)
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
    wgen.write(f"Fk/WitRj{key}.lean", src)
    print(key, tlen)
