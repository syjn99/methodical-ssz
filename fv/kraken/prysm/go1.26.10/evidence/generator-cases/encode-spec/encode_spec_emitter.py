#!/usr/bin/env python3
"""Emitter (evidence tool, not part of gen/generator): per generated encoder fast-path theorem
`Encode.generated_fast`, emit a witness module and a spec-corollary module:
<out dir>/Prysm/<T>/WitnessGeneratedEncodeFastPath.lean and <out dir>/Prysm/<T>/GeneratedEncodeFastPathSpec.lean.

Reads the committed Prysm/<T>/GeneratedEncodeFastPath.lean (statement text, FAST-PATH-JSON header) and the IR (Go struct size).
usage: encode_spec_emitter.py <lean dir> <out dir> [<T> ...]      (<T>: a Go type name of TYPES)
"""
import json, re, sys, os

TYPES = {
    # Go type name: (spec module, SSZ value structure, encoding, serialize lemma, Desc, [(field accessor kind, expr)])
    'Checkpoint': ('Prysm.Checkpoint.Spec', 'Prysm.Checkpoint.SszValue', 'Prysm.Checkpoint.SszValue.encode', 'Prysm.Checkpoint.SszValue.serialize_eq', 'Prysm.Checkpoint.desc', ['u:epoch', 'b:root']),
    'BeaconBlockHeader': ('Prysm.BeaconBlockHeader.Spec', 'Prysm.BeaconBlockHeader.SszValue', 'Prysm.BeaconBlockHeader.SszValue.encode', 'Prysm.BeaconBlockHeader.SszValue.serialize_eq', 'Prysm.BeaconBlockHeader.desc',
           ['u:slot', 'u:proposer', 'b:parent', 'b:state', 'b:body']),
    'Eth1Data': ('Prysm.Eth1Data.Spec', 'Prysm.Eth1Data.SszValue', 'Prysm.Eth1Data.SszValue.encode', 'Prysm.Eth1Data.SszValue.serialize_eq', 'Prysm.Eth1Data.desc',
           ['b:depositRoot', 'u:depositCount', 'b:blockHash']),
    'BlobIdentifier': ('Prysm.BlobIdentifier.Spec', 'Prysm.BlobIdentifier.SszValue', 'Prysm.BlobIdentifier.SszValue.encode', 'Prysm.BlobIdentifier.SszValue.serialize_eq', 'Prysm.BlobIdentifier.desc', ['b:blockRoot', 'u:index']),
    'DepositMessage': ('Prysm.DepositMessage.Spec', 'Prysm.DepositMessage.SszValue', 'Prysm.DepositMessage.SszValue.encode', 'Prysm.DepositMessage.SszValue.serialize_eq', 'Prysm.DepositMessage.desc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount']),
    'Deposit_Data': ('Prysm.Deposit_Data.Spec', 'Prysm.Deposit_Data.SszValue', 'Prysm.Deposit_Data.SszValue.encode', 'Prysm.Deposit_Data.SszValue.serialize_eq', 'Prysm.Deposit_Data.desc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount', 'b:signature']),
    'PendingPartialWithdrawal': ('Prysm.PendingPartialWithdrawal.Spec', 'Prysm.PendingPartialWithdrawal.SszValue', 'Prysm.PendingPartialWithdrawal.SszValue.encode', 'Prysm.PendingPartialWithdrawal.SszValue.serialize_eq', 'Prysm.PendingPartialWithdrawal.desc',
           ['u:index', 'u:amount', 'u:withdrawableEpoch']),
    'SyncCommitteeMessage': ('Prysm.SyncCommitteeMessage.Spec', 'Prysm.SyncCommitteeMessage.SszValue', 'Prysm.SyncCommitteeMessage.SszValue.encode', 'Prysm.SyncCommitteeMessage.SszValue.serialize_eq', 'Prysm.SyncCommitteeMessage.desc',
           ['u:slot', 'b:blockRoot', 'u:validatorIndex', 'b:signature']),
    'PendingConsolidation': ('Prysm.PendingConsolidation.Spec', 'Prysm.PendingConsolidation.SszValue', 'Prysm.PendingConsolidation.SszValue.encode', 'Prysm.PendingConsolidation.SszValue.serialize_eq', 'Prysm.PendingConsolidation.desc', ['u:sourceIndex', 'u:targetIndex']),
    'PendingDeposit': ('Prysm.PendingDeposit.Spec', 'Prysm.PendingDeposit.SszValue', 'Prysm.PendingDeposit.SszValue.encode', 'Prysm.PendingDeposit.SszValue.serialize_eq', 'Prysm.PendingDeposit.desc',
           ['b:pubkey', 'b:withdrawalCredentials', 'u:amount', 'b:signature', 'u:slot']),
    'PowBlock': ('Prysm.PowBlock.Spec', 'Prysm.PowBlock.SszValue', 'Prysm.PowBlock.SszValue.encode', 'Prysm.PowBlock.SszValue.serialize_eq', 'Prysm.PowBlock.desc',
           ['b:blockHash', 'b:parentHash', 'n:totalDifficulty']),
    'HistoricalSummary': ('Prysm.HistoricalSummary.Spec', 'Prysm.HistoricalSummary.SszValue', 'Prysm.HistoricalSummary.SszValue.encode', 'Prysm.HistoricalSummary.SszValue.serialize_eq', 'Prysm.HistoricalSummary.desc',
           ['b:blockSummaryRoot', 'b:stateSummaryRoot']),
    'SigningData': ('Prysm.SigningData.Spec', 'Prysm.SigningData.SszValue', 'Prysm.SigningData.SszValue.encode', 'Prysm.SigningData.SszValue.serialize_eq', 'Prysm.SigningData.desc', ['b:objectRoot', 'b:domain']),
    'SyncAggregatorSelectionData': ('Prysm.SyncAggregatorSelectionData.Spec', 'Prysm.SyncAggregatorSelectionData.SszValue', 'Prysm.SyncAggregatorSelectionData.SszValue.encode', 'Prysm.SyncAggregatorSelectionData.SszValue.serialize_eq', 'Prysm.SyncAggregatorSelectionData.desc', ['u:slot', 'u:subcommitteeIndex']),
    'ValidatorBalance': ('Prysm.ValidatorBalance.Spec', 'Prysm.ValidatorBalance.SszValue', 'Prysm.ValidatorBalance.SszValue.encode', 'Prysm.ValidatorBalance.SszValue.serialize_eq', 'Prysm.ValidatorBalance.desc', ['u:index', 'u:balance']),
    'VoluntaryExit': ('Prysm.VoluntaryExit.Spec', 'Prysm.VoluntaryExit.SszValue', 'Prysm.VoluntaryExit.SszValue.encode', 'Prysm.VoluntaryExit.SszValue.serialize_eq', 'Prysm.VoluntaryExit.desc', ['u:epoch', 'u:validatorIndex']),
}
RTCOPY_LEN = 26


def die(msg):
    sys.stderr.write('encode_spec_emitter: ' + msg + '\n')
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
    path = os.path.join(lean_dir, 'Prysm', X, 'GeneratedEncodeFastPath.lean')
    src = open(path).read()
    hdr = json.loads(re.search(r'FAST-PATH-JSON: (\{.*\})', src).group(1))
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
    mst = re.search(r'\n  stateWord := (true|false)', src)
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
    if st is None:   # hand layouts (Checkpoint, BeaconBlockHeader, Eth1Data) live in `Prysm/<Type>/EncodeFastPathKindInstances.lean`: decide from the binder count
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
    blk = ['word_bytes 0']   # guard at 0x10000
    R = []
    # receiver cells
    o = 0
    while o < gsize:
        if o in rcv:
            v = rcv[o]
            r = role.get(v)
            if r and r[0] == 'ast':
                blk.append('zeros 8')
            elif r and r[0] == 'u':
                blk.append(v)
            elif r and r[0] == 'cap':
                blk.append('word_bytes %d' % fields[r[1]][2])
            else:
                m = re.match(r'^Int\.toBytes 8 (\w+)\.toInt$', v)
                if m and m.group(1) in cont_addr:
                    blk.append('word_bytes 0x%x' % cont_addr[m.group(1)])
                elif re.match(r'^Int\.toBytes 8 \d+$', v):
                    blk.append(v)
                else:
                    die('receiver word ' + v)
            o += 8
        else:
            g0 = o
            while o < gsize and o not in rcv:
                o += 8
            blk.append('zeros %d' % (o - g0))
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
            blk.append('word_bytes 0')
            o += 8
        elif o in stack:
            blk.append('zeros %d' % stklen[o])
            o += stklen[o]
        else:
            g0 = o
            while o < hi and o not in stack and o != 0:
                o += 8
            blk.append('zeros %d' % (o - g0))
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
        blk.append('zeros %d' % f[2])
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
    w('import Runtime.CopyModel')
    w('import Machine.WitnessHost')
    w('')
    w('/-!')
    w('# Witness of `%s_fast` (%s encoder fast path, generated theorem)' % (p, hdr['type']))
    w('')
    w('Emitted by the unit\'s evidence tool `encode_spec_emitter.py` (not the generator) from the committed statement text and')
    w('the IR; then built and kernel-checked. Host: the real Go 1.26.10 `MarshalSSZTo` (index 0)%s.' %
      (' and `MemmoveGrowsliceModel` (index %d, `model_memmove`, S = 0)' % Pl if rt else '; no call on the fast path'))
    w('One memory block at `0x10000`: guard word (r14 = 0xfff0); the receiver at 0x10008 (`prysm/ir/ir-mainnet.json`')
    w('gc amd64 layout, %d bytes; byte fields = (pointer, n, n) with the n bytes after the receiver; unexported tail' % gsize)
    w('zero); the stack window (rsp = 0x%x: rsp − %d … rsp + 23); `dst` at 0x%x: the prefix, the old output' % (rsp, F + 16, dst))
    w('bytes, the spare capacity. Frame `R`: every byte of the block that no premise chunk names, and the spare.')
    w('Two instances: empty prefix with `cap = %d`; prefix `[0xaa, 0xbb, 0xcc]` with 5 spare bytes. For every' % size)
    w('field value of the stated lengths every premise of `%s_fast` holds (non-vacuity of the fast path).' % p)
    w('-/')
    w('')
    w('open Machine Runtime Machine.Witness Codec %s' % ' '.join(info['open'].split()[3:]))
    w('')
    w('namespace Prysm.%s.Witness.GeneratedEncodeFastPath' % X)
    w('')
    w('set_option maxRecDepth 100000')
    w('')
    if rt:
        w('def program : Program := %s ++ MemmoveGrowsliceModel' % C)
        w('')
        w('theorem program_length : program.length = %d := by rfl' % (Pl + RTCOPY_LEN))
    else:
        w('def program : Program := %s' % C)
        w('')
        w('theorem program_length : program.length = %d := by rfl' % Pl)
    w('')
    w('instance host : Host := mkHost program (by rw [program_length]; decide)')
    w('')
    if rt:
        w('theorem placed_at_0 : %s.IsInfixAt Host.prog 0 := infixAt_of [] MemmoveGrowsliceModel (by simp [Host.prog, mkHost, program]) rfl' % C)
        w('theorem placed_copy_model : MemmoveGrowsliceModel.IsInfixAt Host.prog %d := infixAt_of %s [] (by simp [Host.prog, mkHost, program]) (by rfl)' % (Pl, C))
        w('theorem labels_fresh_at_0 : LabelsFresh %s 0 := fun i hi => absurd hi (Nat.not_lt_zero _)' % C)
        w('theorem labels_fresh_copy_model : LabelsFresh MemmoveGrowsliceModel %d := labelsFresh_of (by decide)' % Pl)
    else:
        w('theorem placed_at_0 : %s.IsInfixAt Host.prog 0 := infixAt_of [] [] (by simp [Host.prog, mkHost, program]) rfl' % C)
        w('theorem labels_fresh_at_0 : LabelsFresh %s 0 := fun i hi => absurd hi (Nat.not_lt_zero _)' % C)
    w('')
    w('abbrev zeros (k : Nat) : List UInt8 := List.replicate k 0')
    w('abbrev word_bytes (v : UInt64) : List UInt8 := Int.toBytes 8 v.toBitVec.toInt')
    w('')
    w('def block (%s pre spare : List UInt8) : List UInt8 :=' % plist)
    w('  ' + nest(blk))
    w('')
    w('def mem (%s pre spare : List UInt8) : DataMem := (block %s pre spare).At (0x10000 : BitVec 64)' % (plist, plist))
    w('')
    w('def initial_state (%s pre spare : List UInt8) (zmms : RegZmms) (flags : StatusFlags) : MachineData :=' % plist)
    w('  ⟨⟨0x10008, 0x%x, UInt64.ofNat pre.length, 0, 0, UInt64.ofNat (pre.length + %d + spare.length), 0x%x, 0,' % (dst, size, rsp))
    w('    0, 0, 0, 0, 0, 0, 0xfff0, 0⟩, zmms, flags, mem %s pre spare⟩' % plist)
    w('')

    def inst(name, doc, pre, spare_n):
        spare = '(zeros %d)' % spare_n if spare_n else '[]'
        npre = len(pre)
        prel = '[' + ', '.join('0x%02x' % b for b in pre) + ']'
        pres = prel if pre else '[]'
        Rs = ['Eq ((zeros %d).At (0x%x : BitVec 64))' % (n, a0) for a0, n in R]
        if spare_n:
            Rs.append('Eq ((zeros %d).At (0x%x : BitVec 64))' % (spare_n, dst + npre + size))
        Rexpr = ' ⋆ '.join(Rs) if Rs else 'Std.ExtHashMap.emp'
        args = []
        for names, ty in info['binders']:
            for n in names:
                if n == 'k':
                    args.append('0')
                elif n == 'hk':
                    args.append('placed_at_0')
                elif n == 'hf':
                    args.append('labels_fresh_at_0')
                elif n in role:
                    r = role[n]
                    if r[0] == 'ast':
                        args.append('(zeros 8)')
                    elif r[0] in ('u', 'cont'):
                        args.append(n)
                    elif r[0] == 'cap':
                        args.append('(word_bytes %d)' % fields[r[1]][2])
                    elif r[0] == 'pre':
                        args.append(pres)
                    elif r[0] == 'd':
                        args.append('(zeros %d)' % fields[r[1]][2])
                    elif r[0] == 'ptr':
                        args.append('(0x%x : BitVec 64)' % cont_addr[n])
                elif n in cl['stk']:
                    args.append('(zeros %s)' % cl['lens'][n])
                elif n == 's':
                    args.append('(initial_state %s %s %s zmms flags)' % (plist, pres, spare))
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
                    args.append('(by simp [initial_state])')
                elif n == 'hmm':
                    args.append('(model_memmove %d placed_copy_model labels_fresh_copy_model 0)' % Pl)
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
              '      witness_split [%s]' % ', '.join('h_' + q for q in params),
              '      simp only [initial_state, word_bytes, nil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep, UInt64.toBitVec_ofNat,',
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
        w('      ⟨initial_state %s %s %s zmms flags, Host.addrOf 0⟩ :=' % (plist, pres, spare))
        line = '  eventually_mono (%s_fast %s)' % (p, ' '.join(args))
        line = line.replace('HMEM', '\n    ' + '\n'.join(hm) + '\n   ')
        w(line)
        w('    (fun _ h => ⟨h.1, h.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩)')
        w('')
    inst('runs_empty', 'Empty prefix, `cap = %d`.' % size, [], 0)
    inst('runs_prefix', 'Prefix `[0xaa, 0xbb, 0xcc]`, 5 spare bytes (`cap = len + %d`).' % (size + 5),
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
        w('  runs_%s %s %s z\' f' % (nm, v, pr))
    w('')
    w('end Prysm.%s.Witness.GeneratedEncodeFastPath' % X)
    return '\n'.join(L) + '\n', dict(rsp=rsp, dst=dst, R=R, gsize=gsize)


def emit_spec(X, info, cl):
    hdr = info['hdr']
    fields = hdr['fields']
    p = hdr['prefix']
    sp = p.split('_')[0]
    smod, PS, enc, ser, desc, facc = TYPES[X]
    PS, enc, ser, desc = (n[len('Prysm.%s.' % X):] for n in (PS, enc, ser, desc))  # short names in Prysm.<T>
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
    w('import Runtime.CopyModel')
    w('')
    w('/-!')
    w('# %s encoder fast path (generated theorem) against the independent Desc' % hdr['type'])
    w('')
    w('`Encode.generated_fast_spec`: for a receiver holding the Go layout of `g : %s` (uint64 fields = `uintBytes 8`, byte' % PS)
    w('fields = `(p, n, cap)` with the n bytes at `p`), the generated fast-path theorem `%s_fast` writes at' % p)
    w('`dst[len:len+%d]` exactly the bytes of `serialize %s g.toValue` (the Desc of the decoder\'s spec alignment).' % (hdr['size'], desc))
    w('Shape of `Prysm.BeaconBlockHeader.Encode.fast_path_spec`. Encoder fast path only (`len + %d ≤ cap`, exact field' % hdr['size'])
    w('lengths). Emitted by the unit\'s evidence tool `encode_spec_emitter.py`, then built and kernel-checked.')
    w('-/')
    w('')
    w('open Machine Runtime Codec %s EthLib.Serialization.Ssz' % ' '.join(info['open'].split()[3:]))
    w('variable [Host]')
    w('')
    w('namespace Prysm.%s' % X)
    w('')
    toList = ' ++ '.join(fe[0] for fe in fexpr)
    w('theorem SszValue.encode_toList_generated (g : %s) : (%s g).toList = %s := by' % (PS, enc, toList))
    w('  simp only [%s, Array.toList_append] <;> rfl' % enc)
    w('')
    names = ['A%d' % k for k in range(nfl)]
    hyps = ' '.join('(h%d : A%d.length = %d)' % (k, k, fexpr[k][1]) for k in range(nfl))
    rhs = 'Eq (A0.At a)' + ''.join(' ⋆ Eq (A%d.At (a + %d))' % (k, offs[k]) for k in range(1, nfl))
    w('theorem Encode.generated_fast_split (a : BitVec 64) (%s : List UInt8) %s :' % (' '.join(names), hyps))
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
    w('theorem Encode.generated_fast_spec %s :' % '\n    '.join(out_b))
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
        tac = 'simp [Spec.uintBytes_size]' if fe[2] in ('u', 'n') else 'simp'
        w('  have hF%d : %s.length = %d := by %s' % (k, fe[0], fe[1], tac))
    w('  refine eventually_mono (%s_fast %s)' % (p, ' '.join(args)))
    w('    (fun st ⟨%s⟩ =>' % pat)
    w('      ⟨hpc, hrax, hrbx, hrcx, hrdi, hrsi, ?_⟩)')
    w('  rw [SszValue.encode_toList_generated, Encode.generated_fast_split %s %s]' % (' '.join(['_'] * (nfl + 1)), ' '.join('hF%d' % k for k in range(nfl))))
    w('  simp only [← Std.ExtHashMap.sep_assoc]')
    for k, fe in enumerate(fexpr):
        w('  generalize %s = F%d at hm ⊢' % (fe[0], k))
    w('  exact sep_true (by ecancel)')
    w('')
    w('end Prysm.%s' % X)
    return '\n'.join(L) + '\n'


def main():
    lean_dir, out_dir = sys.argv[1], sys.argv[2]
    which = sys.argv[3:] or list(TYPES)
    ir = json.load(open(os.path.join(lean_dir, '..', 'prysm', 'ir', 'ir-mainnet.json')))
    summary = {}
    for X in which:
        info = parse(lean_dir, X)
        info['module'] = 'Prysm.%s.GeneratedEncodeFastPath' % X
        info['Spath'] = os.path.join(lean_dir, '..', info['hdr']['assembly'])
        if X in ('Checkpoint',):
            info['Spath'] = os.path.join(lean_dir, '..', 'prysm/go1.26.10/link-set/norm/github.com_OffchainLabs_prysm_v7_proto_prysm_v1alpha1.Checkpoint.MarshalSSZTo.S') if not os.path.exists(info['Spath']) else info['Spath']
        cl = classify(info)
        gsize, _ = ir_size(ir, info['hdr']['ir_type'])
        wt, meta = emit_wit(X, info, cl, gsize)
        sp = emit_spec(X, info, cl)
        os.makedirs(os.path.join(out_dir, 'Prysm', X), exist_ok=True)
        open(os.path.join(out_dir, 'Prysm', X, 'WitnessGeneratedEncodeFastPath.lean'), 'w').write(wt)
        open(os.path.join(out_dir, 'Prysm', X, 'GeneratedEncodeFastPathSpec.lean'), 'w').write(sp)
        summary[X] = dict(meta, runtime_calls=any(b[0] == ['hmm'] for b in info['binders']), nex=len(info['exnames']))
    print(json.dumps(summary, indent=1, sort_keys=True))


if __name__ == '__main__':
    main()
