from pathlib import Path
import re,subprocess,importlib.util,collections,struct,hashlib
root=Path.home()/'orca/workspaces/methodical-ssz/ssz-fv-kraken'
b=root/'fv/kraken'; out=Path(__file__).parent
spec=importlib.util.spec_from_file_location('conv',b/'link/conv.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
fns=c.read_objdump(b/'link/out/target.objdump');syms=c.read_nm(b/'link/out/p1bin-amd64.nm')
elf=(b/'link/out/p1bin-amd64').read_bytes();assert elf[:6]==b'\x7fELF\x02\x01'
phoff=struct.unpack_from('<Q',elf,32)[0]; ents,num=struct.unpack_from('<HH',elf,54)
loads=[struct.unpack_from('<IIQQQQQQ',elf,phoff+i*ents) for i in range(num)]
def elfbytes(a,n):
    for typ,flags,off,vaddr,pa,filesz,memsz,align in loads:
        if typ==1 and vaddr<=a and a+n<=vaddr+filesz:return elf[off+a-vaddr:off+a-vaddr+n]
    raise AssertionError(hex(a))
raw={}
for line in (b/'link/out/target.objdump').read_text().splitlines():
    m=re.match(r'\s+\S+\s+0x([0-9a-f]+)\s+([0-9a-f]+)\s+',line)
    if m:raw[int(m[1],16)]=bytes.fromhex(m[2])
llvm=subprocess.check_output(['xcrun','--find','llvm-objdump'],text=True).strip()
refs=collections.Counter();calls=collections.Counter(); normcount=0
for f in fns:
    ins=f['ins'];lo=ins[0][0];hi=ins[-1][0]+ins[-1][1]
    assert next(n for a,n,name in syms if name==f['name'] and a==lo)==hi-lo
    text=subprocess.check_output([llvm,'-d',f'--start-address={lo}',f'--stop-address={hi}',str(b/'link/out/p1bin-amd64')],text=True)
    (out/(c.clean(f['name'])+'.llvm.txt')).write_text(text)
    ll=[];lb={}
    for line in text.splitlines():
        m=re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s+(.+)$',line)
        if not m:continue
        a=int(m[1],16);bb=bytes.fromhex(m[2]);att=re.sub(r'\s+',' ',m[3]).split(' # ')[0].split(' <')[0].replace(', ',',').strip()
        if re.match(r'nop[bwlq]?\b',att):att='nop'
        ll.append((a,len(bb),att));lb[a]=bb
    assert set(lb)=={a for a,n,t in ins},(f['name'],'instruction boundaries')
    for i,(a,n,t) in enumerate(ins):
        assert raw[a]==lb[a]==elfbytes(a,n)
        if i+1<len(ins):assert a+n==ins[i+1][0]
        if t in c.NORM:normcount+=1
        br=c.BRANCH.match(t)
        if br:
            target=int(br[2],16)
            if lo<=target<hi:assert target in lb
            elif t.startswith('call'):calls[c.clean(c.sym_at(syms,target)[0])]+=1
        r=c.RIP.search(t)
        if r:
            name,off=c.sym_at(syms,a+n+int(r[1],0));refs[c.clean(name)]+=1
    name,go=c.convert(f,syms,True)
    assert go==(b/f'link/out/norm/{name}.S').read_text()
    name,ltext=c.convert({'name':f['name'],'ins':ll},syms,True)
    (out/(name+'.llvm.S')).write_text(ltext)
    print(name,len(ins),'ELF bytes, symbol extent, instruction boundaries, local targets, regenerated assembly PASS')
print('RIP references',sum(refs.values()),dict(refs));print('external calls',dict(calls));print('normalized padding',normcount)
# Concrete negative cases accepted by the converter.
bad=out/'converter-missing-comment.objdump'
bad.write_text('TEXT pkg.f(SB) file.go\n file.go:1 0x100 90 NOP // nop\n file.go:2 0x101 48ffc0 INCQ AX\n file.go:3 0x104 c3 RET // retq\n')
assert len(c.read_objdump(bad)[0]['ins'])==2
print('NEGATIVE: converter silently drops an instruction without //')
_,wrong=c.convert({'name':'pkg.f','ins':[(0x100,2,'jmp 0x101'),(0x102,1,'retq')]},[],False)
assert 'jmp L_pkg.f_1' in wrong and 'L_pkg.f_1:' not in wrong
print('NEGATIVE: converter emits undefined label for a jump into an instruction')
assert c.clean('pkg.f[uint8]')==c.clean('pkg.f_uint8_')
print('NEGATIVE: symbol sanitization is not injective')
print('ELF sha256',hashlib.sha256(elf).hexdigest())
