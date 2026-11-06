import sys; sys.path.insert(0,sys.argv[1]); import wgen
# Witnesses of lu_reject_toobig_main / lu_reject_misaligned_main (re-proof R6,
# re-proof fix X5, fix 2 X4): runtime.convT64 (rt_convT64: 8 bytes from the
# bump heap hold the count, the heap case of BoxIn) and fmt.errorf
# (rt_errorf_dw: the constant format, the int box and the errorString) in one
# host and one bump heap. Labels after RtErr: the errorString itab (its type
# word t8 points to a 48-byte type descriptor), 15 fillers, the error global
# (errorString itab, e1; e1 is a 16-byte errorString with the message "err")
# and runtime.staticuint64s (the static entry of the count: StaticBox).
# The input buffer (p, len, len) has all its bytes in the block.
MODE=sys.argv[2]
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
LAB={"toobig":"ssz.ErrListTooBig","misaligned":"ssz.ErrIncorrectListSize"}[MODE]
OFF={"toobig":40290,"misaligned":42646}[MODE]
FDEF={"toobig":"luFmtTooBig","misaligned":"luFmtMis"}[MODE]
FL={"toobig":56,"misaligned":68}[MODE]
RCX={"toobig":4+8*17,"misaligned":5}[MODE]
V={"toobig":17,"misaligned":1}[MODE]          # the boxed count: n, or len - 4
HEAP=8296                                      # >= msg (3) + 8288 (fix 2 X4 budget)
GS=0x10001
ITAB_IDX=5+193+15
ITAB=0x10000+ITAB_IDX   # e0 value: the errorString itab; ITAB + 8 holds t8
LAB_IDX=ITAB_IDX+16; LABA=0x10000+LAB_IDX      # error global: 16 bytes after t8
A40={"toobig":72,"misaligned":40}[MODE]
if MODE=="toobig":
    STK=[("hole1","z 24",24),("a40","z 16",16),("a50","z 16",16),("hole2","z 32",32)]
    RH=f"""Eq ((z 24).At (s.regs.rsp.toBitVec - 96)) ⋆ Eq ((z 32).At (s.regs.rsp.toBitVec - 40))"""
else:
    STK=[("hole1","z 56",56),("a40","z 16",16),("a50","z 16",16)]
    RH=f"""Eq ((z 56).At (s.regs.rsp.toBitVec - 96))"""
ch=[("guard",Z,8),("scratch","z 8",8),("rslot","z 8",8),("spl","z 40",40)]+STK+[("fp","z 8",8),("ra",Z,8),("hole3","z 8",8),("s98","z 8",8)]
a=wgen.CH0+sum(n for _,_,n in ch)
assert a<=ITAB+8, a
G0=ITAB+8-a
ch+=[("gap_t",f"z {G0}",G0),("t8","Int.toBytes 8 (TD#64).toInt",8)]
a=ITAB+16
assert a==LABA, (a, LABA)
ch+=[("e0",f"Int.toBytes 8 ({ITAB}#64).toInt",8),("e1","Int.toBytes 8 (OBJ#64).toInt",8),
     ("b4","[4, 0, 0, 0]",4),("gap_buf",f"z {RCX-4}",RCX-4)]
ch=wgen.aligned(ch+[("eo_sp","SPV",8)],{"eo_sp"},base=wgen.CH0)[:-1]
a=wgen.CH0+sum(n for _,_,n in ch)
OBJ=a; SP=a+16
ch+=[("eo_sp",f"Int.toBytes 8 ({SP}#64).toInt",8),("eo_len","Int.toBytes 8 (BitVec.ofNat 64 3).toInt",8),("emsg","[101, 114, 114]",3)]
a=OBJ+19
# runtime.staticuint64s after NF more filler labels, so that its entry V lies after the chunks above
NF=max(0,a-8*V-(LAB_IDX+1+0x10000))
ST_IDX=LAB_IDX+1+NF; STA=0x10000+ST_IDX
SB=STA+8*V
GB=SB-a; assert GB>=0, GB
ch+=[("gap_sb",f"z {GB}",GB),("sbox",f"Int.toBytes 8 (BitVec.ofNat 64 {V}).toInt",8)]
a=SB+8
G=GS+OFF-a; assert G>=0, G
ch+=[("holeG",f"z {G}",G),("fs",FDEF,FL)]
a=GS+OFF+FL
TDP=(-a)%8; TD=a+TDP
ch+=([("gap_tdp",f"z {TDP}",TDP)] if TDP else [])+[("gap_td","z 48",48)]
ch=[(k,e.replace("OBJ#64",f"{OBJ}#64").replace("TD#64",f"{TD}#64"),n) for k,e,n in ch if n]
R=RH+f"""
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8)) ⋆ Eq ((z {G}).At (label "go_string._" + {OFF-G}).toBitVec)"""
SBX=f"Eq ((Int.toBytes 8 (BitVec.ofNat 64 {V}).toInt).At ((label \"runtime.staticuint64s\").toBitVec + 8 * BitVec.ofNat 64 {V}))"
prem=f"""Eq ((z 40).At (s.regs.rsp.toBitVec - 136)) ⋆ Eq ({FDEF}.At (label "go_string._" + {OFF}).toBitVec) ⋆ Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - {A40})) ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - {A40-16}))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144 - BitVec.ofNat 64 8))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ bumpHeap {HEAP}
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({ITAB} : UInt64).toBitVec.toInt).At (label "{LAB}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({OBJ} : UInt64).toBitVec.toInt).At (label "{LAB}" + 8).toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({TD} : UInt64).toBitVec.toInt).At (({ITAB} : UInt64).toBitVec + 8))
      ⋆ ((Eq ((Int.toBytes 8 ({SP} : BitVec 64).toInt).At ({OBJ} : UInt64).toBitVec)
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({OBJ} : UInt64).toBitVec + 8)))
        ⋆ Eq ([101, 114, 114].At ({SP} : BitVec 64)))
      ⋆ {SBX} ⋆ {R}"""
Rs=R.replace("s.regs","(s0 zmms flags).regs")
NS={"toobig":"WitLuTb","misaligned":"WitLuMa"}[MODE]
THM=f"lu_reject_{MODE}_main"
MID={"toobig":"17 (by decide) ","misaligned":""}[MODE]+f"(s0 zmms flags) 0 0 {ITAB} {OBJ} {TD} (by decide) (by rw [label_itab]; rfl) ({SP} : BitVec 64) [101, 114, 114]"
TAIL={"toobig":"(by simp [s0]) (by simp [s0]) (by simp [s0])","misaligned":"(by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])"}[MODE]
SBRW={"toobig":"","misaligned":", show (s0 zmms flags).regs.rcx.toBitVec - 4 = BitVec.ofNat 64 1 by simp [s0]"}[MODE]
TAILP='[Kraken.Directive.label "go_itab._errors.errorString_error", '+", ".join(f'Kraken.Directive.label "pad_t{i}"' for i in range(15))+', Kraken.Directive.label "'+LAB+'"'+"".join(f', Kraken.Directive.label "pad_s{i}"' for i in range(NF))+', Kraken.Directive.label "runtime.staticuint64s"]'
cfg=dict(ns=NS,imports=["import Fk.LuRejectCall","import Fk.RtErr","import Fk.BumpMore"],doc=f"""# Premise witness of `{THM}` (re-proof R6, fix 2 X4)

ListU64.UnmarshalSSZ on the `{MODE}` error path. Host: data labels
(`go_string._` at 0x10001), the real ListU64.UnmarshalSSZ (index 5), `RtErr`
(`rt_convT64`: the box of {V} on the bump heap; `rt_errorf_dw`: the constant
format `{FDEF}`, the `type:int` word and the errorString), then the
errorString itab (type word → a 48-byte type descriptor), 15 filler labels,
`{LAB}` (errorString itab, e1; e1 → "err") and `runtime.staticuint64s` (the
static entry of {V}). One bump heap of {HEAP} bytes after the other chunks.
The input buffer has all its bytes. Generated by `tools/wit/wlur.py {MODE}`.""",
 target="ListU64UnmarshalSSZ",tlen=193,models=[("rterr","RtErr",15),("fnItab",TAILP,18+NF)],chunks=ch,
 heap=HEAP,heap_end=True,pbinders="",pnames="",lenhyps="",lenhypnames=[f"{FDEF}_len"],
 regs=lambda a: f"0, {hex(a['b4'])}, {RCX}, 0, 0, {RCX}, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0",
 premise=prem,
 main=lambda st: f"""set_option maxHeartbeats 8000000 in
/-- **Non-vacuity of `{THM}`.** convT64 by `rt_convT64` (a real 8-byte box on
the bump heap), the `%d`/`%w` `fmt.errorf` by `rt_errorf_dw`, in one host and
one heap. The decoder returns a non-nil error. -/
theorem {THM.replace('_main','_runs')} (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨s0 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono ({THM} 5 hk_target hf_target {MID}
    (z 8) (z 8) (z 16) (z 16) (z 8) rfl rfl rfl rfl rfl ({Rs} ⋆ fun _ => True) 8 (z 8) (z 40) rfl rfl
    bumpHeap {HEAP} (by decide) (by decide)
    (by rw [errstr_eq{SBRW}, staticBox_small (BitVec.ofNat 64 {V}) (by decide)]
        have h := s_mem zmms flags; simp only [Std.ExtHashMap.sep_assoc] at h ⊢; exact h)
    {TAIL}
    (rt_convT64 {st['rterr']} hk_rterr hf_rterr 8) (rt_errorf_dw {st['rterr']} hk_rterr hf_rterr bumpHeap {FDEF} luTW 8))
    (fun _ h => ⟨h.1, h.2.1⟩)
""")
src,addr,starts=wgen.gen(cfg)
assert starts["fnItab"]==ITAB_IDX, starts
src=src.replace('.label "pad1"','.label "go_string._"',1)
src=src.replace("abbrev z (k : Nat) : List UInt8 := List.replicate k 0",f"""set_option maxRecDepth 100000 in
theorem label_err : label "{LAB}" = {LABA} :=
  mk_label P _ {LAB_IDX} _ (by simp [P, dataLabels]; rfl) (by decide)

set_option maxRecDepth 100000 in
theorem label_gs : label "go_string._" = 0x10001 :=
  mk_label P _ 1 _ (by simp [P, dataLabels]) (by decide)

set_option maxRecDepth 100000 in
theorem label_itab : label "go_itab._errors.errorString_error" = {ITAB} :=
  mk_label P _ {ITAB_IDX} _ (by simp [P, dataLabels]; rfl) (by decide)

set_option maxRecDepth 100000 in
theorem label_st : label "runtime.staticuint64s" = {STA} :=
  mk_label P _ {ST_IDX} _ (by simp [P, dataLabels]; rfl) (by decide)

theorem errstr_eq : ErrStr ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114]
    = (Eq ((Int.toBytes 8 ({SP} : BitVec 64).toInt).At ({OBJ} : UInt64).toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({OBJ} : UInt64).toBitVec + 8)))
      ⋆ Eq ([101, 114, 114].At ({SP} : BitVec 64)) := by
  unfold ErrStr ErrObj
  rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
  rfl

theorem staticBox_small (v : BitVec 64) (h : v.toNat < 256) :
    StaticBox v = Eq ((Int.toBytes 8 v.toInt).At ((label "runtime.staticuint64s").toBitVec + 8 * v)) := if_pos h

abbrev z (k : Nat) : List UInt8 := List.replicate k 0""",1)
src=src.replace("  rw [label_wb]\n","  rw [label_wb, label_gs, label_err, label_st]\n  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat, BitVec.reduceAdd, BitVec.reduceMul]\n",1)
src=src.replace("set_option maxHeartbeats 8000000 in\nset_option maxRecDepth 100000 in\ntheorem s_mem","set_option maxHeartbeats 32000000 in\nset_option maxRecDepth 100000 in\ntheorem s_mem",1)
open(f"Fk/{NS}.lean","w").write(src)
print(NS, addr["ra"], OBJ, SB, TD, starts)
