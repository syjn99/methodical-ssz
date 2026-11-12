#!/usr/bin/env python3
"""Emitter (evidence tool, not part of gen/scal): per generated encoder fast-path theorem
`<p>_g6e_fast`, emit a witness module (WitE2c<X>.lean) and a spec-corollary module (E2cSpec<X>.lean).

Reads the committed Gen6<X>Enc.lean (statement text, GEN6-JSON header) and the IR (Go struct size).
usage: e2cemit.py <lean dir> <out dir> [X ...]
"""
import json, re, sys, os

TYPES = {
    # X: (spec module, P structure, enc, serialize lemma, Desc, [(field accessor kind, expr)])
    'Cp': ('E2e.Spec', 'PCp', 'pcpEnc', 'pcp_serialize', 'prysmCpDesc', ['u:epoch', 'b:root']),
    'Bh': ('E2eScal.BhSpec', 'PBh', 'pbhEnc', 'pbh_serialize', 'prysmBhDesc',
           ['u:slot', 'u:proposer', 'b:parent', 'b:state', 'b:body']),
    'E1': ('E2eScal.E1Spec', 'PE1', 'pe1Enc', 'pe1_serialize', 'prysmE1Desc',
           ['b:depositRoot', 'u:depositCount', 'b:blockHash']),
    'Bi': ('E2eScal.BiSpec', 'PBi', 'pbiEnc', 'pbi_serialize', 'prysmBiDesc', ['b:blockRoot', 'u:index']),
    'Dm': ('E2eScal.DmSpec', 'PDm', 'pdmEnc', 'pdm_serialize', 'prysmDmDesc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount']),
    'Dd': ('E2eScal.DdSpec', 'PDd', 'pddEnc', 'pdd_serialize', 'prysmDdDesc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount', 'b:signature']),
    'Pw': ('E2eScal.PwSpec', 'PPw', 'ppwEnc', 'ppw_serialize', 'prysmPwDesc',
           ['u:index', 'u:amount', 'u:withdrawableEpoch']),
    'Sc': ('E2eScal.SmSpec', 'PSm', 'psmEnc', 'psm_serialize', 'prysmSmDesc',
           ['u:slot', 'b:blockRoot', 'u:validatorIndex', 'b:signature']),
    'Pc': ('E2eScal.PcSpec', 'PPc', 'ppcEnc', 'ppc_serialize', 'prysmPcDesc', ['u:sourceIndex', 'u:targetIndex']),
    'Pd': ('E2eScal.PdSpec', 'PPd', 'ppdEnc', 'ppd_serialize', 'prysmPdDesc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount', 'b:signature', 'u:slot']),
    'Pb': ('E2eScal.PbSpec', 'PPb', 'ppbEnc', 'ppb_serialize', 'prysmPbDesc',
           ['b:blockHash', 'b:parentHash', 'n:totalDifficulty']),
    'Hs': ('E2eScal.HsSpec', 'PHs', 'phsEnc', 'phs_serialize', 'prysmHsDesc',
           ['b:blockSummaryRoot', 'b:stateSummaryRoot']),
    'Sd': ('E2eScal.SdSpec', 'PSd', 'psdEnc', 'psd_serialize', 'prysmSdDesc', ['b:objectRoot', 'b:domain']),
    'Sa': ('E2eScal.SaSpec', 'PSa', 'psaEnc', 'psa_serialize', 'prysmSaDesc', ['u:slot', 'u:subcommitteeIndex']),
    'Vb': ('E2eScal.VbSpec', 'PVb', 'pvbEnc', 'pvb_serialize', 'prysmVbDesc', ['u:index', 'u:balance']),
    'Ve': ('E2eScal.VeSpec', 'PVe', 'pveEnc', 'pve_serialize', 'prysmVeDesc', ['u:epoch', 'u:validatorIndex']),
}
RTCOPY_LEN = 26


def die(msg):
    sys.stderr.write('e2cemit: ' + msg + '\n')
    sys.exit(2)


def groups(text):
    """Top-level balanced paren groups of a binder list, until a ',' at depth 0."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == '(':
            d, j = 0, i
            while True:
                if text[j] == '(':
                    d += 1
                elif text[j] == ')':
                    d -= 1
                    if d == 0:
                        break
                j += 1
            out.append(text[i + 1:j])
            i = j + 1
        elif c == ',':
            return out, text[i + 1:]
        else:
            i += 1
    die('no end of binders')


def split_top(s, sep):
    out, d, cur = [], 0, ''
    i = 0
    while i < len(s):
        c = s[i]
        if c == '(':
            d += 1
        elif c == ')':
            d -= 1
        if d == 0 and s.startswith(sep, i):
            out.append(cur)
            cur = ''
            i += len(sep)
            continue
        cur += c
        i += 1
    out.append(cur)
    return [x.strip() for x in out]


def parse(lean_dir, X):
    path = os.path.join(lean_dir, 'E2eScal', 'Gen6%sEnc.lean' % X)
    src = open(path).read()
    hdr = json.loads(re.search(r'GEN6-JSON: (\{.*\})', src).group(1))
    opn = re.search(r'^open (.*)$', src, re.M).group(1)
    p = hdr['prefix']
    m = re.search(r'theorem %s_fast : ∀ (.*?):= by' % p, src, re.S)
    if not m:
        die('no fast theorem in ' + path)
    stmt = m.group(1)
    gs, rest = groups(stmt)
    binders = []
    for g in gs:
        names, ty = g.split(' : ', 1)
        binders.append((names.split(), ty.strip()))
    mst = re.search(r'\n  st := (true|false)', src)
    st = (mst.group(1) == 'true') if mst else None
    nex = 0
    mex = re.search(r'∃ \(([\w ]+) : List UInt8\)', rest)
    exnames = mex.group(1).split() if mex else []
    return dict(hdr=hdr, open=opn, binders=binders, rest=rest, st=st, exnames=exnames, src=src, path=path)


def ir_size(ir, irtype):
    pkg, name = irtype.split('.')

    def walk(o):
        if isinstance(o, dict):
            if 'go_fields' in o:
                yield o
            for v in o.values():
                yield from walk(v)
        elif isinstance(o, list):
            for v in o:
                yield from walk(v)
    hits = [t for t in walk(ir) if t.get('name') == name and t.get('package', '').endswith('/' + pkg)]
    if len(hits) != 1:
        die('IR type %s: %d hits' % (irtype, len(hits)))
    t = hits[0]
    end = max(f['offset_gc_amd64'] + f['size_gc_amd64'] for f in t['go_fields'])
    al = t.get('go_align_gc_amd64', 8)
    return (end + al - 1) // al * al, [(f['name'], f['offset_gc_amd64']) for f in t['go_fields'] if f['exported']]


ADDR_RE = re.compile(r'^Eq \((.*)\.At (.*)\)$')


def chunk(c):
    m = ADDR_RE.match(c)
    if not m:
        die('chunk form: ' + c)
    val, addr = m.group(1), m.group(2)
    if val.startswith('(') and val.endswith(')'):
        val = val[1:-1]
    if addr.startswith('(') and addr.endswith(')'):
        addr = addr[1:-1]
    return val, addr


def classify(info):
    hdr, B = info['hdr'], info['binders']
    fields = hdr['fields']
    nU = sum(1 for f in fields if f[1] == 'u')
    nB = sum(1 for f in fields if f[1] == 'b')
    lists = [b for b in B if b[1] == 'List UInt8']
    xs = lists[0][0]
    st = info['st']
    if st is None:   # hand layouts (Checkpoint, BeaconBlockHeader, Eth1Data) live in EncTies: decide from the binder count
        st = len(xs) == 1 + nU + 2 * nB + 1 + len(fields)
    exp = (1 if st else 0) + nU + 2 * nB + 1 + len(fields)
    if len(xs) != exp:
        die('xs group length %d != %d' % (len(xs), exp))
    i = 0
    role = {}
    if st:
        role[xs[0]] = ('ast',)
        i = 1
    ufs = [k for k, f in enumerate(fields) if f[1] == 'u']
    bfs = [k for k, f in enumerate(fields) if f[1] == 'b']
    for k in ufs:
        role[xs[i]] = ('u', k)
        i += 1
    for k in bfs:
        role[xs[i]] = ('cap', k)
        i += 1
    for k in bfs:
        role[xs[i]] = ('cont', k)
        i += 1
    role[xs[i]] = ('pre',)
    i += 1
    for k in range(len(fields)):
        role[xs[i]] = ('d', k)
        i += 1
    stk = [b for b in lists[1:] if b[0] != ['scratch']]
    stknames = stk[0][0] if stk else []
    ptrs = [b[0] for b in B if b[1] == 'BitVec 64']
    ptrs = ptrs[0] if ptrs else []
    if len(ptrs) != nB:
        die('pointer count')
    for j, pn in enumerate(ptrs):
        role[pn] = ('ptr', bfs[j])
    lens = {}
    for names, ty in B:
        m = re.match(r'^(\w+)\.length = (\w+)$', ty)
        if m and len(names) == 1:
            lens[m.group(1)] = m.group(2)
    hmem = [ty for names, ty in B if names == ['h_mem']][0]
    assert hmem.startswith('s.dmem =⋆ ')
    chunks = [chunk(c) for c in split_top(hmem[len('s.dmem =⋆ '):], '⋆') if c.strip() != 'R']
    return dict(role=role, xs=xs, stk=stknames, ptrs=ptrs, lens=lens, chunks=chunks, ufs=ufs, bfs=bfs)


def off(addr, base):
    if addr == base:
        return 0
    m = re.match(r'^%s ([+-]) (\d+)$' % re.escape(base), addr)
    if not m:
        return None
    return int(m.group(2)) * (1 if m.group(1) == '+' else -1)


def emit_wit(X, info, cl, gsize):
    hdr = info['hdr']
    fields = hdr['fields']
    C = hdr['const']
    p = hdr['prefix']
    sp = p.split('_')[0]
    rt = any(b[0] == ['hmm'] for b in info['binders'])
    F = hdr['frame']
    size = hdr['size']
    role = cl['role']
    # ---- receiver words
    rcv = {}
    content_order = []
    stack = {}
    for val, addr in cl['chunks']:
        o = off(addr, 's.regs.rax.toBitVec')
        if o is not None:
            rcv[o] = val
            continue
        if addr == 's.regs.rsp.toBitVec':
            continue
        o = off(addr, 's.regs.rsp.toBitVec')
        if o is not None:
            stack[o] = val
            continue
        if addr.startswith('s.regs.rsp.toBitVec - ') and addr.endswith(' - BitVec.ofNat 64 S'):
            continue
        if addr == 's.regs.r14.toBitVec + 16':
            continue
        if addr in cl['ptrs']:
            content_order.append((addr, val))
            continue
        if addr.startswith('s.regs.rbx.toBitVec'):
            continue
        die('unclassified chunk %s @ %s' % (val, addr))
    base = 0x10008
    cont_addr = {}
    a = base + gsize
    for pn, val in content_order:
        cont_addr[pn] = a
        a += fields[role[pn][1]][2]
    wb = a
    rsp = wb + F + 16
    dst = rsp + 24
    blk = ['w 0']   # guard at 0x10000
    R = []
    # receiver cells
    o = 0
    while o < gsize:
        if o in rcv:
            v = rcv[o]
            r = role.get(v)
            if r and r[0] == 'ast':
                blk.append('z 8')
            elif r and r[0] == 'u':
                blk.append(v)
            elif r and r[0] == 'cap':
                blk.append('w %d' % fields[r[1]][2])
            else:
                m = re.match(r'^Int\.toBytes 8 (\w+)\.toInt$', v)
                if m and m.group(1) in cont_addr:
                    blk.append('w 0x%x' % cont_addr[m.group(1)])
                elif re.match(r'^Int\.toBytes 8 \d+$', v):
                    blk.append(v)
                else:
                    die('receiver word ' + v)
            o += 8
        else:
            g0 = o
            while o < gsize and o not in rcv:
                o += 8
            blk.append('z %d' % (o - g0))
            R.append((base + g0, o - g0))
    for pn, val in content_order:
        blk.append(val)
    # stack cells from rsp - (F+16) to rsp + 24
    lo, hi = -(F + 16), 24
    stklen = {}
    for so, v in stack.items():
        n = cl['lens'].get(v)
        if n is None or not n.isdigit():
            die('stack chunk length ' + v)
        stklen[so] = int(n)
    o = lo
    while o < hi:
        if o == 0:
            blk.append('w 0')
            o += 8
        elif o in stack:
            blk.append('z %d' % stklen[o])
            o += stklen[o]
        else:
            g0 = o
            while o < hi and o not in stack and o != 0:
                o += 8
            blk.append('z %d' % (o - g0))
            R.append((rsp + g0, o - g0))
    # check stack chunks do not overlap
    occ = set()
    for so, n in stklen.items():
        for b in range(so, so + n):
            if b in occ:
                die('stack overlap')
            occ.add(b)
    # dst
    blk.append('pre')
    for k, f in enumerate(fields):
        blk.append('z %d' % f[2])
    blk.append('spare')
    uparams = [n for n in cl['xs'] if role[n][0] == 'u']
    bparams = [n for n in cl['xs'] if role[n][0] == 'cont']
    params = uparams + bparams
    plen = {n: (8 if role[n][0] == 'u' else fields[role[n][1]][2]) for n in params}

    def nest(items):
        s = items[-1]
        for it in reversed(items[:-1]):
            s = '%s ++ (%s)' % (paren(it), s)
        return s

    def paren(t):
        return t if re.match(r'^\w+$', t) else '(' + t + ')'
    plist = ' '.join(params)
    Pl = len(open(info['Spath']).read().rstrip('\n').split('\n'))
    L = []
    w = L.append
    w('import %s' % info['module'])
    w('import Fk.RtCopy')
    w('import Fk.WHost')
    w('')
    w('/-!')
    w('# Witness of `%s_fast` (%s encoder fast path, generated theorem; unit E2-C)' % (p, hdr['type']))
    w('')
    w('Emitted by the unit\'s evidence tool `e2cemit.py` (not the generator) from the committed statement text and')
    w('the IR; then built and kernel-checked. Host: the real Go 1.26.10 `MarshalSSZTo` (index 0)%s.' %
      (' and `RtCopy` (index %d, `rt_memmove`, S = 0)' % Pl if rt else '; no call on the fast path'))
    w('One memory block at `0x10000`: guard word (r14 = 0xfff0); the receiver at 0x10008 (`prysm/ir/ir-mainnet.json`')
    w('gc amd64 layout, %d bytes; byte fields = (pointer, n, n) with the n bytes after the receiver; unexported tail' % gsize)
    w('zero); the stack window (rsp = 0x%x: rsp − %d … rsp + 23); `dst` at 0x%x: the prefix, the old output' % (rsp, F + 16, dst))
    w('bytes, the spare capacity. Frame `R`: every byte of the block that no premise chunk names, and the spare.')
    w('Two instances: empty prefix with `cap = %d`; prefix `[0xaa, 0xbb, 0xcc]` with 5 spare bytes. For every' % size)
    w('field value of the stated lengths every premise of `%s_fast` holds (non-vacuity of the fast path).' % p)
    w('-/')
    w('')
    w('open Fk Fk.W E2eScal E2eScal.Gen6Enc %s' % ' '.join(info['open'].split()[2:]))
    w('')
    w('namespace E2eScal.WitE2c%s' % X)
    w('')
    w('set_option maxRecDepth 100000')
    w('')
    if rt:
        w('def P : Program := %s ++ RtCopy' % C)
        w('')
        w('theorem P_len : P.length = %d := by rfl' % (Pl + RTCOPY_LEN))
    else:
        w('def P : Program := %s' % C)
        w('')
        w('theorem P_len : P.length = %d := by rfl' % Pl)
    w('')
    w('instance host : Host := mkHost P (by rw [P_len]; decide)')
    w('')
    if rt:
        w('theorem hk0 : %s.IsInfixAt Host.prog 0 := infixAt_of [] RtCopy (by simp [Host.prog, mkHost, P]) rfl' % C)
        w('theorem hkR : RtCopy.IsInfixAt Host.prog %d := infixAt_of %s [] (by simp [Host.prog, mkHost, P]) (by rfl)' % (Pl, C))
        w('theorem hf0 : LabelsFresh %s 0 := fun i hi => absurd hi (Nat.not_lt_zero _)' % C)
        w('theorem hfR : LabelsFresh RtCopy %d := labelsFresh_of (by decide)' % Pl)
    else:
        w('theorem hk0 : %s.IsInfixAt Host.prog 0 := infixAt_of [] [] (by simp [Host.prog, mkHost, P]) rfl' % C)
        w('theorem hf0 : LabelsFresh %s 0 := fun i hi => absurd hi (Nat.not_lt_zero _)' % C)
    w('')
    w('abbrev z (k : Nat) : List UInt8 := List.replicate k 0')
    w('abbrev w (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt')
    w('')
    w('def block (%s pre spare : List UInt8) : List UInt8 :=' % plist)
    w('  ' + nest(blk))
    w('')
    w('def mem (%s pre spare : List UInt8) : DataMem := (block %s pre spare).At (0x10000 : BitVec 64)' % (plist, plist))
    w('')
    w('def cs0 (%s pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=' % plist)
    w('  ⟨⟨0x10008, 0x%x, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + %d + spare.length), 0x%x, 0,' % (dst, size, rsp))
    w('    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem %s pre spare⟩' % plist)
    w('')

    def inst(name, doc, pre, spare_n):
        spare = '(z %d)' % spare_n if spare_n else '[]'
        npre = len(pre)
        prel = '[' + ', '.join('0x%02x' % b for b in pre) + ']'
        pres = prel if pre else '[]'
        Rs = ['Eq ((z %d).At (0x%x : BitVec 64))' % (n, a0) for a0, n in R]
        if spare_n:
            Rs.append('Eq ((z %d).At (0x%x : BitVec 64))' % (spare_n, dst + npre + size))
        Rexpr = ' ⋆ '.join(Rs) if Rs else 'Std.ExtHashMap.emp'
        args = []
        for names, ty in info['binders']:
            for n in names:
                if n == 'k':
                    args.append('0')
                elif n == 'hk':
                    args.append('hk0')
                elif n == 'hf':
                    args.append('hf0')
                elif n in role:
                    r = role[n]
                    if r[0] == 'ast':
                        args.append('(z 8)')
                    elif r[0] in ('u', 'cont'):
                        args.append(n)
                    elif r[0] == 'cap':
                        args.append('(w %d)' % fields[r[1]][2])
                    elif r[0] == 'pre':
                        args.append(pres)
                    elif r[0] == 'd':
                        args.append('(z %d)' % fields[r[1]][2])
                    elif r[0] == 'ptr':
                        args.append('(0x%x : BitVec 64)' % cont_addr[n])
                elif n in cl['stk']:
                    args.append('(z %s)' % cl['lens'][n])
                elif n == 's':
                    args.append('(cs0 %s %s %s zmms flags)' % (plist, pres, spare))
                elif n in ('ra', 'guard'):
                    args.append('0')
                elif n == 'hpre':
                    args.append('rfl')
                elif n == 'R':
                    args.append('(%s)' % Rexpr)
                elif n == 'S':
                    args.append('0')
                elif n == 'scratch':
                    args.append('[]')
                elif n == 'hsc':
                    args.append('rfl')
                elif n == 'h_mem':
                    args.append('HMEM')
                elif n in ('hguard', 'hsp', 'hcap', 'hcap63'):
                    args.append('(by simp [cs0])')
                elif n == 'hmm':
                    args.append('(rt_memmove %d hkR hfR 0)' % Pl)
                elif re.match(r'^h\w+$', n):
                    m = re.match(r'^(\w+)\.length = ', ty)
                    tgt = m.group(1) if m else None
                    if tgt in params:
                        args.append('h_' + tgt)
                    else:
                        args.append('rfl')
                else:
                    die('binder ' + n)
        hm = ['(by',
              '      have H : Eq ((block %s %s %s).At (0x10000 : BitVec 64))' % (plist, pres, spare),
              '        (mem %s %s %s) := rfl' % (plist, pres, spare),
              '      wit_split [%s]' % ', '.join('h_' + q for q in params),
              '      simp only [cs0, w, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,',
              '        BitVec.ofNat_eq_ofNat, BitVec.reduceAdd, BitVec.reduceSub, List.length_nil, List.length_cons,',
              '        List.length_replicate, show (UInt64.ofNat %d).toBitVec = %d#64 from rfl] at H ⊢' % (npre, npre),
              '      simp only [Std.ExtHashMap.sep_assoc] at H ⊢',
              '      simp only [Std.ExtHashMap.sep_comm, Std.ExtHashMap.sep_comm_l] at H ⊢',
              '      exact H)']
        sig = ' '.join('(%s : List UInt8)' % q for q in params)
        hs = ' '.join('(h_%s : %s.length = %d)' % (q, q, plen[q]) for q in params)
        w('set_option maxHeartbeats 16000000 in')
        w('/-- %s -/' % doc)
        w('theorem %s %s' % (name, sig))
        w('    %s' % hs)
        w('    (zmms : RegZmms) (flags : StatusFlags) :')
        w('    Eventually (step1 Host.exe)')
        w('      (fun st => st.pc = Int64.ofBitVec (0 : UInt64).toBitVec ∧ st.data.regs.rax = 0x%x' % dst)
        w('        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0)')
        w('      ⟨cs0 %s %s %s zmms flags, Host.addrOf 0⟩ :=' % (plist, pres, spare))
        line = '  eventually_mono (%s_fast %s)' % (p, ' '.join(args))
        line = line.replace('HMEM', '\n    ' + '\n'.join(hm) + '\n   ')
        w(line)
        w('    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)')
        w('')
    inst('%s_e2c_wit_empty' % sp, 'Empty prefix, `cap = %d`.' % size, [], 0)
    inst('%s_e2c_wit_prefix' % sp, 'Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + %d`).' % (size + 5),
         [0xaa, 0xbb, 0xcc], 5)

    def vals(kind):
        out = []
        for q in params:
            n = plen[q]
            if role[q][0] == 'u':
                v = {'zero': '0', 'mid': '0x0123456789abcdef', 'max': '(2 ^ 64 - 1)'}[kind]
                out.append('(Int.toBytes 8 %s)' % v)
            else:
                v = {'zero': '0', 'mid': '0x5a', 'max': '0xff'}[kind]
                out.append('(List.replicate %d %s)' % (n, v))
        prf = []
        for q in params:
            prf.append('(by decide)' if role[q][0] == 'u' else 'rfl')
        return ' '.join(out), ' '.join(prf)
    for nm, kind in (('empty', 'zero'), ('prefix', 'mid'), ('prefix', 'max')):
        v, pr = vals(kind)
        w('example (z\' : RegZmms) (f : StatusFlags) :=')
        w('  %s_e2c_wit_%s %s %s z\' f' % (sp, nm, v, pr))
    w('')
    w('end E2eScal.WitE2c%s' % X)
    return '\n'.join(L) + '\n', dict(rsp=rsp, dst=dst, R=R, gsize=gsize)


def emit_spec(X, info, cl):
    hdr = info['hdr']
    fields = hdr['fields']
    p = hdr['prefix']
    sp = p.split('_')[0]
    smod, PS, enc, ser, desc, facc = TYPES[X]
    role = cl['role']
    fexpr = []
    for k, fa in enumerate(facc):
        kind, nm = fa.split(':')
        if kind == 'u':
            fexpr.append(('(uintBytes 8 g.%s.toNat).toList' % nm, 8, 'u'))
        elif kind == 'b':
            fexpr.append(('g.%s.toList' % nm, fields[k][2], 'b'))
        else:
            fexpr.append(('(uintBytes 32 g.%s.val).toList' % nm, 32, 'n'))
        exp = 'u' if fields[k][1] == 'u' else 'b'
        if (kind == 'u') != (exp == 'u'):
            die('field kind mismatch %s %s' % (X, fa))
    sub = {}
    for n, r in role.items():
        if r[0] in ('u', 'cont'):
            sub[n] = fexpr[r[1]][0]
    drop = set(sub)

    def subst(t):
        for n, e in sub.items():
            t = re.sub(r'\b%s\b' % re.escape(n), lambda _m, e=e: e, t)
        return t
    B = []
    for names, ty in info['binders']:
        if names == ['k'] or names == ['hk'] or names == ['hf']:
            pass
        keep = [n for n in names if n not in drop]
        m = re.match(r'^(\w+)\.length = ', ty)
        if m and m.group(1) in drop:
            continue
        if not keep:
            continue
        B.append((keep, subst(ty)))
    # insert g after hf
    out_b = []
    for names, ty in B:
        out_b.append('(%s : %s)' % (' '.join(names), ty))
        if names == ['hf']:
            out_b.append('(g : %s)' % PS)
    nfl = len(fields)
    offs = []
    o = 0
    for fe in fexpr:
        offs.append(o)
        o += fe[1]
    # args for the fast theorem
    args = []
    for names, ty in info['binders']:
        for n in names:
            if n in sub:
                args.append('(%s)' % sub[n] if not sub[n].startswith('(') else sub[n])
            elif re.match(r'^h\w+$', n) and re.match(r'^(\w+)\.length = ', ty) and \
                    re.match(r'^(\w+)\.length = ', ty).group(1) in sub:
                k = role[re.match(r'^(\w+)\.length = ', ty).group(1)][1]
                args.append('hF%d' % k)
            else:
                args.append(n)
    nex = len(info['exnames'])
    pat = 'hpc, hrax, hrbx, hrcx, hrdi, hrsi, _, _, _, ' + ', '.join(['_'] * (2 * nex)) + (', ' if nex else '') + 'hm'
    L = []
    w = L.append
    w('import %s' % info['module'])
    w('import %s' % smod)
    w('import Fk.RtCopy')
    w('')
    w('/-!')
    w('# %s encoder fast path (generated theorem) against the independent Desc (unit E2-C)' % hdr['type'])
    w('')
    w('`%s_e2c_spec_k`: for a receiver holding the Go layout of `g : %s` (uint64 fields = `uintBytes 8`, byte' % (sp, PS))
    w('fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `%s_fast` writes at' % p)
    w('`dst[len:len+%d]` exactly the bytes of `serialize %s g.toValue` (the Desc of the decoder\'s spec alignment).' % (hdr['size'], desc))
    w('Shape of `E2eScal.Bh.bh_e2e_marshal_spec_k`. Encoder fast path only (`len + %d ≤ cap`, exact field' % hdr['size'])
    w('lengths). Emitted by the unit\'s evidence tool `e2cemit.py`, then built and kernel-checked.')
    w('-/')
    w('')
    w('open Fk E2e E2eScal E2eScal.Gen6Enc %s EthLib.Serialization.Ssz' % ' '.join(info['open'].split()[2:]))
    w('variable [Host]')
    w('')
    w('namespace E2eScal.E2c')
    w('')
    toList = ' ++ '.join(fe[0] for fe in fexpr)
    w('theorem %s_e2c_enc_toList (g : %s) : (%s g).toList = %s := by' % (sp, PS, enc, toList))
    w('  simp only [%s, Array.toList_append] <;> rfl' % enc)
    w('')
    names = ['A%d' % k for k in range(nfl)]
    hyps = ' '.join('(h%d : A%d.length = %d)' % (k, k, fexpr[k][1]) for k in range(nfl))
    rhs = 'Eq (A0.At a)' + ''.join(' ⋆ Eq (A%d.At (a + %d))' % (k, offs[k]) for k in range(1, nfl))
    w('theorem %s_e2c_split (a : BitVec 64) (%s : List UInt8) %s :' % (sp, ' '.join(names), hyps))
    w('    Eq ((%s).At a) = %s := by' % (' ++ '.join(names), rhs))
    if nfl > 2:
        w('  simp only [List.append_assoc]')
    rws = []
    for k in range(nfl - 1):
        hs = ', '.join('h%d' % j for j in range(k, nfl))
        first = '(by rw [h%d]; rfl)' % k if k == 0 else '(by rw [h%d]; bv_omega)' % k
        lhs = 'a' if k == 0 else 'a + %d' % offs[k]
        rws.append('at_app A%d _ (b := a + %d) %s (by simp [%s])' % (k, offs[k + 1], first, hs))
    w('  rw [' + ',\n    '.join(rws) + ']')
    if nfl > 2:
        w('  simp only [Std.ExtHashMap.sep_assoc]')
    w('')
    w('set_option maxHeartbeats 4000000 in')
    w('theorem %s_e2c_spec_k %s :' % (sp, '\n    '.join(out_b)))
    w('    ∃ bs, serialize %s g.toValue = .ok bs ∧' % desc)
    w('    Eventually (step1 Host.exe)')
    w('      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx')
    w('        ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + %d ∧ st.data.regs.rcx = s.regs.rdi' % hdr['size'])
    w('        ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0')
    w('        ∧ (Eq (pre.At s.regs.rbx.toBitVec) ⋆ Eq (bs.toList.At (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec))')
    w('          ⋆ fun _ => True) st.data.dmem)')
    w('      ⟨s, Host.addrOf k⟩ := by')
    w('  refine ⟨%s g, %s g, ?_⟩' % (enc, ser))
    for k, fe in enumerate(fexpr):
        tac = 'simp [Fv.uintBytes_size]' if fe[2] in ('u', 'n') else 'simp'
        w('  have hF%d : %s.length = %d := by %s' % (k, fe[0], fe[1], tac))
    w('  refine eventually_mono (%s_fast %s)' % (p, ' '.join(args)))
    w('    (fun st ⟨%s⟩ =>' % pat)
    w('      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)')
    w('  rw [%s_e2c_enc_toList, %s_e2c_split %s %s]' % (sp, sp, ' '.join(['_'] * (nfl + 1)), ' '.join('hF%d' % k for k in range(nfl))))
    w('  simp only [← Std.ExtHashMap.sep_assoc]')
    for k, fe in enumerate(fexpr):
        w('  generalize %s = F%d at hm ⊢' % (fe[0], k))
    w('  exact sep_true (by ecancel)')
    w('')
    w('end E2eScal.E2c')
    return '\n'.join(L) + '\n'


def main():
    lean_dir, out_dir = sys.argv[1], sys.argv[2]
    which = sys.argv[3:] or list(TYPES)
    ir = json.load(open(os.path.join(lean_dir, '..', 'prysm', 'ir', 'ir-mainnet.json')))
    summary = {}
    for X in which:
        info = parse(lean_dir, X)
        info['module'] = 'E2eScal.Gen6%sEnc' % X
        info['Spath'] = os.path.join(lean_dir, '..', info['hdr']['S'])
        if X in ('Cp',):
            info['Spath'] = os.path.join(lean_dir, '..', 'prysm/go1.26.10/e2e/link/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S') if not os.path.exists(info['Spath']) else info['Spath']
        cl = classify(info)
        gsize, _ = ir_size(ir, info['hdr']['ir_type'])
        wt, meta = emit_wit(X, info, cl, gsize)
        sp = emit_spec(X, info, cl)
        open(os.path.join(out_dir, 'WitE2c%s.lean' % X), 'w').write(wt)
        open(os.path.join(out_dir, 'E2cSpec%s.lean' % X), 'w').write(sp)
        summary[X] = dict(meta, rt=any(b[0] == ['hmm'] for b in info['binders']), nex=len(info['exnames']))
    print(json.dumps(summary, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
