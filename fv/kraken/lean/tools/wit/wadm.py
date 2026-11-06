import sys; sys.path.insert(0,sys.argv[1]); import wgen
Z="Int.toBytes 8 (0 : UInt64).toBitVec.toInt"
PL=int(sys.argv[2]) if len(sys.argv)>2 else 3
addrs=wgen.addrs
ch=[("guard",Z,8),("rslot","z 8",8),("gap1","z 88",88),("l144","z 8",8),("l136","z 8",8),("l128","z 8",8),("l120","z 8",8),
    ("gap2","z 32",32),("l80","z 8",8),("l72","z 8",8),("gap3","z 56",56),("fp","z 8",8),("ra",Z,8),("s8","z 8",8),("s16","z 8",8),
    ("e0","e0",8),("e1","e1",8),("pp","Int.toBytes 8 (PP : BitVec 64).toInt",8),("c32","Int.toBytes 8 32",8),("gap4","Int.toBytes 8 32",8),
    ("pps","Int.toBytes 8 (PS : BitVec 64).toInt",8),("ppt","Int.toBytes 8 (PT : BitVec 64).toInt",8),
    ("root","root",32),("se","se",8),("pp1","Int.toBytes 8 (P1 : BitVec 64).toInt",8),("c32s","Int.toBytes 8 32",8),("gap_sc","Int.toBytes 8 32",8),("sroot","sroot",32),
    ("te","te",8),("pp2","Int.toBytes 8 (P2 : BitVec 64).toInt",8),("c32t","Int.toBytes 8 32",8),("gap_tc","Int.toBytes 8 32",8),("troot","troot",32),
    ("pre","pre",PL),("d0","z 8",8),("d1","z 8",8),("d2","z 32",32),("d3","z 8",8),("d4","z 32",32),("d5","z 8",8),("d6","z 32",32)]
ad=addrs(ch)
sub={"PP":hex(ad["root"]),"PS":hex(ad["se"]),"PT":hex(ad["te"]),"P1":hex(ad["sroot"]),"P2":hex(ad["troot"])}
def S(e):
    for k,v in sub.items(): e=e.replace(k+" :",v+" :")
    return e
ch=[(k,S(e),n) for k,e,n in ch]
ins="e0 e1 root se sroot te troot"
prem=f"""Eq (({Z}).At s.regs.rsp.toBitVec)
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 8)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 72)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 120)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 128))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 136)) ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 144))
      ⋆ Eq ((z 8).At (s.regs.rsp.toBitVec - 240)) ⋆ Eq (([] : List UInt8).At (s.regs.rsp.toBitVec - 240 - BitVec.ofNat 64 0))
      ⋆ Eq (({Z}).At (s.regs.r14.toBitVec + 16))
      ⋆ Eq (e0.At s.regs.rax.toBitVec) ⋆ Eq (e1.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 ({sub['PP']} : BitVec 64).toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24))
      ⋆ Eq ((Int.toBytes 8 ({sub['PS']} : BitVec 64).toInt).At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ((Int.toBytes 8 ({sub['PT']} : BitVec 64).toInt).At (s.regs.rax.toBitVec + 48)) ⋆ Eq (root.At ({sub['PP']} : BitVec 64))
      ⋆ Eq (se.At ({sub['PS']} : BitVec 64)) ⋆ Eq ((Int.toBytes 8 ({sub['P1']} : BitVec 64).toInt).At (({sub['PS']} : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 32).At (({sub['PS']} : BitVec 64) + 16))
      ⋆ Eq (sroot.At ({sub['P1']} : BitVec 64))
      ⋆ Eq (te.At ({sub['PT']} : BitVec 64)) ⋆ Eq ((Int.toBytes 8 ({sub['P2']} : BitVec 64).toInt).At (({sub['PT']} : BitVec 64) + 8)) ⋆ Eq ((Int.toBytes 8 32).At (({sub['PT']} : BitVec 64) + 16))
      ⋆ Eq (troot.At ({sub['P2']} : BitVec 64))
      ⋆ Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 8))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 16))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 48))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 56))
      ⋆ Eq ((z 8).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 88))
      ⋆ Eq ((z 32).At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec + 96))"""
cfg=dict(ns="WitAdM",imports=["import Fk.AdMarshal"],
 doc=f"""# Premise witness of `ad_marshal_main` (1b-fix X4)

Host: data labels, the real AttestationData.MarshalSSZTo (index 5) and
`RtCopy` (`rt_memmove`). For every 128 bytes of field values and every
{PL}-byte destination prefix, `s0` meets every premise of `ad_marshal_main`
(three memmove calls) and the encoder returns length {PL} + 128.
A symbolic prefix length made the memory lemma time out (REPORT-1b-fix X4).""",
 target="PrysmAttestationDataMarshalSSZTo",tlen=335,models=[("rtcopy","RtCopy",26)],chunks=ch,
 pbinders=f"({ins} pre : List UInt8)",pnames=ins+" pre",
 lenhyps=f"(h0 : e0.length = 8) (h1 : e1.length = 8) (hroot : root.length = 32) (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32) (hpl : pre.length = {PL})",
 lenhypnames=["h0","h1","hroot","hse","hsroot","hte","htroot","hpl"],
 regs=lambda a: f"{hex(a['e0'])}, {hex(a['pre'])}, {PL}, 0, 0, {PL+128}, {hex(a['ra'])}, 0, 0, 0, 0, 0, 0, 0, {hex(a['guard']-16)}, 0",
 premise=prem,
 main=lambda st: f"""/-- **Non-vacuity of `ad_marshal_main`.** Every premise holds in this host, the
memmove contract by `rt_memmove`; the encoder returns length {PL} + 128. -/
theorem ad_marshal_runs ({ins} pre : List UInt8) (h0 : e0.length = 8) (h1 : e1.length = 8) (hroot : root.length = 32)
    (hse : se.length = 8) (hsroot : sroot.length = 32) (hte : te.length = 8) (htroot : troot.length = 32)
    (hpl : pre.length = {PL}) (zmms : RegZmms) (flags : StatusFlags) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rbx.toNat = {PL} + 128)
      ⟨s0 {ins} pre zmms flags, Host.addrOf 5⟩ :=
  eventually_mono (ad_marshal_main 5 hk_target hf_target {ins} pre (z 8) (z 8) (z 32) (z 8) (z 32) (z 8) (z 32)
    h0 h1 hroot hse hsroot hte htroot rfl rfl rfl rfl rfl rfl rfl
    {sub['PP']} {sub['PS']} {sub['PT']} {sub['P1']} {sub['P2']}
    (s0 {ins} pre zmms flags) 0 0 (by simp [s0, hpl])
    (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) (z 8) rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun _ => True) 0 [] rfl (s_mem {ins} pre h0 h1 hroot hse hsroot hte htroot hpl zmms flags)
    (by decide) (by decide) (by simp [s0]) (by simp [s0]) (by simp [s0]) (by simp [s0])
    (rt_memmove {st['rtcopy']} hk_rtcopy hf_rtcopy 0))
    (fun _ h => ⟨h.1, by rw [h.2.2.1]; simp [s0]⟩)
""")
src,addr,st=wgen.gen2(cfg)
open('Fk/WitAdM.lean','w').write(src)
