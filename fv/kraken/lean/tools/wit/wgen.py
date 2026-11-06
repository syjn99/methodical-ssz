"""Witness generator: block layout from 0x10000 and the matching Lean pieces.

`python3 tools/wit/wgen.py` (from fv/kraken/lean) runs every generator in ALL.
"""
import subprocess, sys

CH0 = 0x10010  # gen: first address after write barrier, bump pointer and gap

# Every generated file: generator and arguments (output Fk/<file>.lean).
ALL = """wacc sc
wacc vbv
wadm 3
wbl 1
wbl 257
wblm 1
wblm 257
wblr
wblri
wbv
wbvr
wcomp
wcompsc
wlce
wlca 1
wlca 4
wlca 1 1x1
wlca 16,16,16,16 4x16
wlca 0,1,16 Mix
wlcm 0
wlcm 1
wlcm 4
wlcm 1 1x1
wlcm 16,16,16,16 4x16
wlcm 0,1,16 Mix
wlcs 0
wlcs 1
wlcs 4
wlcz zero
wlcz past
wlcz tail
wlug
wlur toobig
wlur misaligned
wmar sc
wmar fv
wmar lu0
wmar lu1
wmar lu16
wmar bv
wmrej lu
wmrej fv
wmrej cp
wne 0
wne 1
wne 16
wnem 0
wnem 1
wnem 16
wnes 0
wnes 1
wnes 16
wrej
wscrb
wsize
wvbvr"""

def sub(src, old, new, count=-1):
    """str.replace that fails when `old` does not occur (a template change)."""
    assert old in src, f"template text not found: {old[:80]!r}"
    return src.replace(old, new, count)

def addrs(ch, a=65536):
    """Start address of every chunk (gen2 layout: the block starts at 0x10000)."""
    ad = {}
    for k, e, n in ch: ad[k] = a; a += n
    return ad

def post_ac(src, hb="4000000"):
    """gen2 output with an empty gap frame and a plain ac_rfl close, 32M heartbeats."""
    src = src.replace("  apply sep_true (F := )\n", "  apply sep_true (F := Std.ExtHashMap.emp)\n  simp only [Std.ExtHashMap.sep_emp]\n", 1)  # only without gaps
    src = sub(src, "  first | (refine Eq.mp ?_ H; exact congrFun (by ac_rfl) _) | ecancel", "  refine Eq.mp ?_ H\n  exact congrFun (by ac_rfl) _", 1)
    return sub(src, f"set_option maxHeartbeats {hb} in\nset_option maxRecDepth 100000 in\ntheorem s_mem", "set_option maxHeartbeats 32000000 in\nset_option maxRecDepth 100000 in\ntheorem s_mem", 1)

def aligned(ch, keys, base=65536, al=8):
    """Insert zero gap chunks so that every chunk whose key is in `keys` starts
    at a multiple of `al` (Go objects and uint64/pointer slice data).
    base: address of the first chunk (gen with a heap at the start: CH0 + heap)."""
    out, a = [], base
    for k, e, n in ch:
        if k in keys and a % al:
            pad = al - a % al
            out.append((f"gap_al_{k}", f"z {pad}", pad)); a += pad
        out.append((k, e, n)); a += n
    return out

def layout(chunks, heap, heap_end=False):
    # chunks: list of (key, lean_expr, length); first three fixed: wb, ptr, heap.
    # heap_end: the heap goes after the chunks (when a label offset such as
    # go_string._+526 must not fall into the heap); ptr then holds its address.
    # A 4-byte gap after the bump pointer (label index 4, 0x10004) puts the heap
    # and the first chunk at 0x10010: Go objects, rsp and heap blocks 8-aligned.
    # The chunks then start at CH0 (heap_end) or CH0 + heap.
    base=65536
    if heap_end:
        hp=CH0+sum(n for _,_,n in chunks)
        hpad=(-hp)%8
        tail=[("gap_al_heap",f"z {hpad}",hpad)] if hpad else []
        items=[("wb","[0, 0, 0, 0]",4),("ptr",f"Int.toBytes 8 ({hex(hp+hpad)} : BitVec 64).toInt",8),("gap_hp","z 4",4)]+chunks+tail+[("heap",f"z {heap}",heap)]
    else:
        items=[("wb","[0, 0, 0, 0]",4),("ptr",f"Int.toBytes 8 ({hex(CH0)} : BitVec 64).toInt",8),("gap_hp","z 4",4),("heap",f"z {heap}",heap)]+chunks
    addr={}; a=base; out=[]
    for k,e,n in items:
        addr[k]=a; out.append((k,e,n,a)); a = a + n if isinstance(n,int) else a
    return out,addr,a

def block_def(name, params, out):
    es=[f"({e})" if (" " in e and not e.startswith("[")) else e for _,e,_,_ in out]
    body=es[-1]
    for e in reversed(es[:-1]): body=f"{e} ++ ({body})"
    return f"def {name} {params}: List UInt8 :=\n  {body}\n"

def host(c, hf_inline):
    """Header, program, host and the infix facts hk_* (and hf_* when hf_inline)."""
    pieces=[("target",c["target"],c["tlen"])]+c["models"]
    starts={}; a=5
    for k,d,n in pieces: starts[k]=a; a+=n
    total=a
    P=" ++ ".join(["dataLabels"]+[d for _,d,_ in pieces])
    L=[]
    L.append("\n".join(c["imports"])+"\nimport Fk.RtCopy\nimport Fk.WHost\n")
    L.append(f"/-!\n{c['doc']}\n-/\n\nopen Fk Fk.Code Fk.W{c.get('opens','')}\n\nnamespace Fk.{c['ns']}\n")
    L.append('def dataLabels : Program :=\n  [.label "runtime.writeBarrier", .label "pad1", .label "pad2", .label "pad3", .label "runtime.fvBump"]\n')
    L.append(f"def P : Program := {P}\n")
    L.append(f"set_option maxRecDepth 100000 in\ntheorem P_len : P.length = {total} := by rfl\n")
    L.append("instance host : Host := mkHost P (by rw [P_len]; decide)\n\ntheorem prog_eq : Host.prog = P := rfl\n")
    for i,(k,d,n) in enumerate(pieces):
        pre=["dataLabels"]+[pd for _,pd,_ in pieces[:i]]
        suf=[sd for _,sd,_ in pieces[i+1:]]
        sufs=" ++ ".join(suf) if suf else "[]"
        s0=starts[k]
        if i==0:
            L.append(f"theorem hk_{k} : {d}.IsInfixAt Host.prog {s0} := by\n  rw [prog_eq]; exact ⟨{sufs}, by simp [P, dataLabels]⟩\n")
        else:
            prel="(" + " ++ ".join(pre) + ")"
            lens=" ".join(f"show {pd}.length = {pn} from by rfl," for _,pd,pn in pieces[:i])
            L.append(f"set_option maxRecDepth 100000 in\ntheorem hk_{k} : {d}.IsInfixAt Host.prog {s0} := by\n  rw [prog_eq]\n  have h : {prel}.length = {s0} := by\n    simp only [List.length_append, {lens.rstrip(',')}]; rfl\n"
                     f"  exact ⟨{sufs}, by rw [show P = {prel} ++ ({d} ++ {sufs}) by simp only [P, List.append_assoc, List.append_nil], List.drop_left' h]; try simp only [List.append_assoc]⟩\n")
        if hf_inline:
            L.append(f"set_option maxRecDepth 100000 in\ntheorem hf_{k} : LabelsFresh {d} {s0} := labelsFresh_of (by rw [prog_eq]; decide)\n")
    return L, pieces, starts

def frame_s0(L, c, out, addr):
    pn=c["pnames"]; pb=c["pbinders"]
    L.append(block_def("block",pb+" ",out))
    L.append(f"def mem {pb} : DataMem := (block {pn}).At (0x10000 : BitVec 64)\n")
    L.append(f"def s0 {pb} (zmms : RegZmms) (flags : StatusFlags) : MachineData :=\n  ⟨⟨{c['regs'](addr)}⟩, zmms, flags, mem {pn}⟩\n")

def gen(c):
    out,addr,end=layout(c["chunks"],c["heap"],c.get("heap_end",False))
    HA=addr["heap"]
    L,pieces,starts=host(c, False)
    for k,d,n in pieces:
        s0=starts[k]
        if k in ("target","rtcopy","rterr") or k.startswith("fn"):
            L.append(f"set_option maxRecDepth 100000 in\ntheorem hf_{k} : LabelsFresh {d} {s0} := labelsFresh_of (by rw [prog_eq]; decide)\n")
        else:
            lab={"makeslice":"runtime.makeslice","newobject":"runtime.newobject"}[k]
            L.append(f'''set_option maxRecDepth 100000 in
theorem hf_{k} : ∀ i < {s0}, Host.prog[i]? ≠ some (.label "{lab}") := by
  have hl : "{lab}" ∉ labs (P.take {s0}) := by decide
  intro i hi hp
  apply hl; apply mem_labs; rw [List.mem_iff_getElem?]
  exact ⟨i, by rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hi h)]; exact hp⟩
''')
    L.append('''set_option maxRecDepth 100000 in
theorem label_wb : label "runtime.writeBarrier" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])

set_option maxRecDepth 100000 in
theorem label_bump : label "runtime.fvBump" = 0x10004 :=
  mk_label P _ 4 _ (by simp [P, dataLabels]) (by decide)

abbrev z (k : Nat) : List UInt8 := List.replicate k 0
''')
    pn=c["pnames"]; pb=c["pbinders"]
    frame_s0(L, c, out, addr)
    lh=c["lenhyps"]; lhn=c["lenhypnames"]
    # The gap atoms are typed like the block's atoms (`@Eq (ExtHashMap ..)`, not
    # `@Eq DataMem`); otherwise ac_rfl sees two atoms.
    gaps=[f"Eq (α := Std.ExtHashMap (BitVec 64) UInt8) (({e}).At {a}#64)" for k,e,n,a in out if k.startswith("gap")]
    parts=[f"Eq (({e}).At {a}#64)" if " " in e and not e.startswith("[") else f"Eq ({e}.At {a}#64)" for k,e,n,a in out if k not in ("ptr","heap")]+c.get("extra_h2",[])
    H2=f"((Eq ((Int.toBytes 8 ({HA}#64).toInt).At 65540#64) ⋆ Eq ((z {c['heap']}).At {HA}#64))\n      ⋆ ("+"\n        ⋆ ".join(parts)+f")) (mem {pn})"
    gapline=f"  apply sep_true (F := {' ⋆ '.join(gaps)})\n" if gaps else "  apply sep_true (F := Std.ExtHashMap.emp)\n  simp only [Std.ExtHashMap.sep_emp]\n"
    simpl=', '.join(lhn)
    L.append(f'''set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem s_mem {pb} {lh} (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 {pn} zmms flags
    s.dmem =⋆ {c["premise"]} ⋆ fun _ => True := by
  intro s
{c.get('pre_tac','')}  have H : Eq ((block {pn}).At (0x10000 : BitVec 64)) (mem {pn}) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil{', ' + simpl if simpl else ''}{c.get('extra_simp','')}]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd{', ' + simpl if simpl else ''}{c.get('extra_simp','')},
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
  have H2 : {H2} := by
    ecancel
  have H3 := sep_mono_left (P' := bumpHeap {c["heap"]}) (fun m hm => ⟨{HA}#64, by decide, by rw [label_bump]; exact hm⟩) H2
  rw [label_wb]
  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
{gapline}  have hu0 : (UInt64.toBitVec 0) = 0#64 := rfl
  have huN : ∀ n : Nat, (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := fun _ => rfl
  simp only [hu0, huN] at H3 ⊢
  refine Eq.mp ?_ H3
  exact congrFun (by ac_rfl) _
''')
    L.append(c["main"](starts))
    L.append(f"end Fk.{c['ns']}\n")
    return "\n".join(L), addr, starts

def gen2(c):
    """No heap, no write barrier; chunks whose key starts with 'gap' fold into the True frame."""
    base=65536; out=[]; addr={}; a=base
    for k,e,n in c["chunks"]:
        addr[k]=a; out.append((k,e,n,a)); a = a + n if isinstance(n,int) else None
    L,pieces,starts=host(c, True)
    if c.get("wb"):
        L.append('''set_option maxRecDepth 100000 in
theorem label_wb : label "runtime.writeBarrier" = 0x10000 :=
  mk_label P _ 0 _ (by simp [P, dataLabels]) (by simp [labs])
''')
    L.append("abbrev z (k : Nat) : List UInt8 := List.replicate k 0\n")
    pn=c["pnames"]; pb=c["pbinders"]
    frame_s0(L, c, out, addr)
    def at(k,e,a):
        ee=f"({e})" if " " in e and not e.startswith("[") else e
        return f"Eq ({ee}.At {a})"
    fixed=[(k,e,a) for k,e,n,a in out if isinstance(n,int)]
    gaps=[at(k,e,f"{a}#64").replace("Eq (","Eq (α := Std.ExtHashMap (BitVec 64) UInt8) (",1) for k,e,a in fixed if k.startswith("gap")]
    lh=c["lenhyps"]; lhn=c["lenhypnames"]
    simpl=', '.join(lhn)
    L.append(f'''set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem s_mem {pb} {lh} (zmms : RegZmms) (flags : StatusFlags) :
    let s := s0 {pn} zmms flags
    s.dmem =⋆ {c["premise"]} ⋆ fun _ => True := by
  intro s
  have H : Eq ((block {pn}).At (0x10000 : BitVec 64)) (mem {pn}) := rfl
  conv at H => lhs; unfold block
  repeat rw [Mem.At_append_sep _ _ _ (by simp only [List.length_append, List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil{', ' + simpl if simpl else ''}]; omega)] at H
  simp only [List.length_replicate, Int.toBytes_length, List.length_cons, List.length_nil, Nat.reduceAdd{', ' + simpl if simpl else ''},
    BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H
{"  rw [label_wb]" + chr(10) if c.get("wb") else ""}  simp only [s, s0, UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub,
    Int64.toBitVec_ofNat, nil_At_emp, Std.ExtHashMap.sep_emp]
  apply sep_true (F := {' ⋆ '.join(gaps)})
  have hu0 : (UInt64.toBitVec 0) = 0#64 := rfl
  have huN : ∀ n : Nat, (UInt64.ofNat n).toBitVec = BitVec.ofNat 64 n := fun _ => rfl
  simp only [hu0, huN] at H ⊢
  try simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceAdd] at H ⊢  -- fold `4#64 + a` after huN (re-proof fix X4)
  first | (refine Eq.mp ?_ H; exact congrFun (by ac_rfl) _) | ecancel
''')
    L.append(c["main"](starts))
    L.append(f"end Fk.{c['ns']}\n")
    return "\n".join(L), addr, starts

if __name__ == "__main__":
    here = sys.argv[0].rsplit("/", 1)[0]
    for line in ALL.splitlines():
        g, *args = line.split()
        r = subprocess.run([sys.executable, f"{here}/{g}.py", here] + args, capture_output=True, text=True)
        if r.returncode: print("FAIL", line, r.stderr.strip().splitlines()[-1])
