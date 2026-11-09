import sys; sys.path.insert(0,sys.argv[1]); import wgen
# Witness of lc_reject_item_main (fix 3 review M4): ListC.UnmarshalSSZ on one
# element of 2 bytes (list bytes [4,0,0,0, 1,2]). One host, one bump heap: the
# real ListC.UnmarshalSSZ, the bump makeslice and 24-byte newobject, the real
# ListU64.UnmarshalSSZ (LuURejShortC by lu_urej_short_holds), RtErr
# (rt_errorf_w: the constant format lcFmtItems). After the models: the
# errorString itab (its type word -> the ELF's *errors.errorString descriptor
# errorStringPtrType), 15 fillers and ssz.ErrSize, initialized (itab, e1; e1 ->
# a 16-byte errorString "err"). go_string._ at 0x10001 (lcFmtItems at +2158).
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
N=1; T=6
TL=[4,0,0,0,1,2]
TLS="["+", ".join(map(str,TL))+"]"
HEAP=8300                      # >= 32 + 24 + 9 + 3 + 8192
GS=0x10001; OFF=2158; FL=9
LAB="ssz.ErrSize"
ITAB_IDX=5+432+6+6+193+15      # dataLabels, ListC, BumpAlloc, BumpNew24, ListU64, RtErr
ITAB=0x10000+ITAB_IDX
LAB_IDX=ITAB_IDX+16; LABA=0x10000+LAB_IDX
ch=[("guard",Z,8),("blk","z 144",144),("rslot","z 8",8),("l224","z 8",8),("l216","z 8",8),("l208","z 8",8),
    ("l200","z 8",8),("l192","z 8",8),
    ("l184","z 8",8),("l176","z 8",8),("l168","z 8",8),("l160","z 8",8),("l152","z 8",8),("l144","z 8",8),("l136","z 8",8),("l128","z 8",8),
    ("b0","z 16",16),("gap2b","z 96",96),
    ("fp","z 8",8),("ra",Z,8),("s8","z 8",8),("slot","z 8",8),("gap3","z 8",8),("s32","z 8",8),
    ("cP","z 8",8),("cL","z 8",8),("cC","z 8",8),
    ("b4","[4, 0, 0, 0]",4),("t0","(lcTl.take 4)",4),("t1","(lcTl.drop 4)",T-4)]
a=wgen.CH0+sum(n for _,_,n in ch)
G0=ITAB+8-a; assert G0>=0, G0
ch+=[("gap_t",f"z {G0}",G0),("t8","Int.toBytes 8 (TD#64).toInt",8)]
assert ITAB+16==LABA
ch+=[("e0",f"Int.toBytes 8 ({ITAB}#64).toInt",8),("e1","Int.toBytes 8 (OBJ#64).toInt",8)]
ch=wgen.aligned(ch+[("eo_sp","SPV",8)],{"eo_sp"},base=wgen.CH0)[:-1]
OBJ=wgen.CH0+sum(n for _,_,n in ch); SP=OBJ+16
ch+=[("eo_sp",f"Int.toBytes 8 ({SP}#64).toInt",8),("eo_len","Int.toBytes 8 (BitVec.ofNat 64 3).toInt",8),("emsg","[101, 114, 114]",3)]
a=SP+3
TDP=(-a)%8; TD=a+TDP
ch+=([("gap_tdp",f"z {TDP}",TDP)] if TDP else [])+[("td","errorStringPtrType",56)]
a=TD+56
G=GS+OFF-a; assert G>=0, G
ch+=[("gap_hole",f"z {G}",G),("fs","lcFmtItems",FL)]
ch=[(k,e.replace("OBJ#64",f"{OBJ}#64").replace("TD#64",f"{TD}#64"),n) for k,e,n in ch if n]
prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 32))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 128)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 136))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 152))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 160)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 168))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 176)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 184))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 224)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 216))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 208))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 232)) ⋆ Eq ((z 144).At (s.regs.rsp.toBitVec - 232 - 144 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16)) ⋆ bumpHeap {HEAP}
      ⋆ Eq ([4, 0, 0, 0].At s.regs.rbx.toBitVec) ⋆ Eq ((lcTl.take 4).At (s.regs.rbx.toBitVec + 4))
      ⋆ Eq ((lcTl.drop 4).At (s.regs.rbx.toBitVec + 4 + 4))
      ⋆ Eq ((z 8).At s.regs.rax.toBitVec) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 8)) ⋆ Eq ((z 8).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 200)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 192))
      ⋆ Eq ((z 16).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (lcFmtItems.At (label "go_string._" + {OFF}).toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({ITAB} : UInt64).toBitVec.toInt).At (label "{LAB}").toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({OBJ} : UInt64).toBitVec.toInt).At (label "{LAB}" + 8).toBitVec)
      ⋆ Eq ((Int.toBytes 8 ({TD}#64).toInt).At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ (Eq ((Int.toBytes 8 ({SP} : BitVec 64).toInt).At ({OBJ} : UInt64).toBitVec)
        ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({OBJ} : UInt64).toBitVec + 8)))
      ⋆ Eq ([101, 114, 114].At ({SP} : BitVec 64))
      ⋆ Eq (errorStringPtrType.At ({TD} : BitVec 64))"""
TAILP='[Kraken.Directive.label "go_itab._errors.errorString_error", '+", ".join(f'Kraken.Directive.label "pad_t{i}"' for i in range(15))+f', Kraken.Directive.label "{LAB}"]'
cfg=dict(ns="WitLcI",opens=" Fv1 EthLib.Serialization.Ssz",imports=["import Fk.LcItems","import Fk.BumpMore","import Fk.RtErr"],
 doc=f"""# Premise witness of `lc_reject_item_main` (fix 3 review M4)

ListC.UnmarshalSSZ on the list bytes {TLS}: one element of 2 bytes, too
short for a ListU64. Host: data labels (`go_string._` at 0x10001,
`lcFmtItems` at +{OFF}), the real ListC.UnmarshalSSZ (index 5), the bump
`runtime.makeslice` and 24-byte `runtime.newobject`, the real
ListU64.UnmarshalSSZ (`LuURejShortC` by `lu_urej_short_holds`), `RtErr`
(`rt_errorf_w`), then the errorString itab (type word → the ELF's
`*errors.errorString` descriptor `errorStringPtrType`), 15 fillers and
`{LAB}` (itab, e1; e1 → "err"). One heap of {HEAP} bytes after the other
chunks. The decoder returns a non-nil error. Generated by `tools/wit/wlci.py`.""",
 target="ListCUnmarshalSSZ",tlen=432,
 models=[("makeslice","BumpAlloc",6),("newobject","BumpNew24",6),("fnLu","ListU64UnmarshalSSZ",193),("rterr","RtErr",15),("fnItab",TAILP,17)],
 chunks=ch,heap=HEAP,heap_end=True,pbinders="",pnames="",lenhyps="",
 lenhypnames=["lcTl_t0","lcTl_t1","lcFmtItems_len","errorStringPtrType_len"],
 regs=lambda a: f"{hex(a['cP'])}, {hex(a['b4'])}, {4+T}, 0, 0, {4+T}, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0",
 premise=prem,
 main=lambda st: f"""set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Non-vacuity of `lc_reject_item_main`.** Every premise holds in this
host: makeslice by `bump_makeslice`, newobject by `bump_newobject24`,
`LuURejShortC` by `lu_urej_short_holds` on the real ListU64 code, the `%w`
`fmt.errorf` by `rt_errorf_w`. The decoder returns a non-nil error. -/
theorem lc_reject_item_runs (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax ≠ 0)
      ⟨s0 zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (lc_reject_item_main 5 hk_target hf_target lcTl {T} {N} (by decide) rfl (by decide) (by decide)
    (by decide) (by decide) lcTl_first
    (s0 zmms flags) 0 0
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 144)
    (z 8) (z 8) (z 8) (z 16)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl 0 (by decide) rfl
    {ITAB} {OBJ} (Int.toBytes 8 ({TD}#64).toInt) [101, 114, 114] [101, 114, 114] ({SP} : BitVec 64)
    (Int.toBytes_length 8 _) (by rw [label_itab]; rfl) (by rw [label_itab]; decide)
    Std.ExtHashMap.emp (fun _ m h => h = m) rfl
    (Eq (errorStringPtrType.At ({TD} : BitVec 64)) ⋆ fun _ => True) bumpHeap {HEAP} (by decide)
    (by rw [errobj_eq]
        simp only [lcFmtItems_addr]
        have h := s_mem zmms flags
        simp only [Std.ExtHashMap.sep_assoc, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep] at h ⊢; exact h)
    (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])
    (bump_makeslice {st['makeslice']} hk_makeslice hf_makeslice _)
    (bump_newobject24 {st['newobject']} hk_newobject hf_newobject _)
    (lu_urej_short_holds {st['fnLu']} hk_fnLu hf_fnLu 0 (by decide))
    (rt_errorf_w {st['rterr']} hk_rterr hf_rterr bumpHeap lcFmtItems Std.ExtHashMap.emp (fun _ m h => h = m) _))
    (fun _ h => ⟨h.1, h.2.1⟩)
""")
src,addr,st=wgen.gen(cfg)
assert st["fnItab"]==ITAB_IDX, st
src=wgen.sub(src,'.label "pad1"','.label "go_string._"',1)
src=wgen.sub(src,"abbrev z (k : Nat) : List UInt8 := List.replicate k 0",f"""set_option maxRecDepth 100000 in
theorem label_gs : label "go_string._" = 0x10001 :=
  mk_label P _ 1 _ (by simp [P, dataLabels]) (by decide)

set_option maxRecDepth 100000 in
theorem label_itab : label "go_itab._errors.errorString_error" = {ITAB} :=
  mk_label P _ {ITAB_IDX} _ (by simp [P, dataLabels]; rfl) (by decide)

set_option maxRecDepth 100000 in
theorem label_err : label "{LAB}" = {LABA} :=
  mk_label P _ {LAB_IDX} _ (by simp [P, dataLabels]; rfl) (by decide)

theorem errobj_eq : ErrObj ({OBJ} : UInt64).toBitVec ({SP} : BitVec 64) [101, 114, 114]
    = Eq ((Int.toBytes 8 ({SP} : BitVec 64).toInt).At ({OBJ} : UInt64).toBitVec)
      ⋆ Eq ((Int.toBytes 8 (BitVec.ofNat 64 3).toInt).At (({OBJ} : UInt64).toBitVec + 8)) := by
  unfold ErrObj
  rw [Mem.At_append_sep _ _ _ (by simp [Int.toBytes_length])]
  rfl

abbrev z (k : Nat) : List UInt8 := List.replicate k 0

/-- The list bytes: offset 4, then 2 element bytes. -/
def lcTl : List UInt8 := {TLS}
theorem lcTl_t0 : (lcTl.take 4).length = 4 := by decide
theorem lcTl_t1 : (lcTl.drop 4).length = {T-4} := by decide
theorem lcTl_first : lcTl.take 4 = (uintBytes 4 (4 * {N})).toList := by decide""",1)
src=wgen.sub(src,"  rw [label_wb]\n","  rw [label_wb, label_gs, label_itab, label_err]\n  simp only [Int64.toBitVec_add, Int64.toBitVec_ofNat, BitVec.reduceAdd, BitVec.reduceMul]\n",1)
wgen.write("Fk/WitLcI.lean", src)
print(addr["cP"], addr["ra"], ITAB, OBJ, SP, TD, st)
