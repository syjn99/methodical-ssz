"""Write prysm/go1.26.10/evidence/flat-types/negative-cases-flat-types.json (cases for gen/checks/negative.py).
Per decoder type: spec_k control; mutants of the generated accept theorem (post rax), the generated size-reject
theorem (post rax), spec_k (hlen + 1), the accept witness (post rax). Per encoder type: spec control; mutants of the
generated fast-path theorem (post rax), the spec corollary (hcap weakened by 8), the witness (post rax)."""
import json, os, re, sys
L = sys.argv[1]   # fv/kraken/lean
DEC = ['DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest', 'BlobSidecarsByRangeRequest',
       'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity']
ENC = ['BeaconBlocksByRangeRequest', 'BuilderDepositRequest', 'BuilderPreferences', 'BlobSidecarsByRangeRequest',
       'DepositRequest', 'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity']
# the negative case id: <Go type in kebab case>-<theorem without its type namespace>-<kind>[-<mutated text>]
# (the rule of all negative case files)
STOP = {'st', 'data', 'regs', 's', 'Eq', 'toBitVec', 'At', 'toList', 'bs', 'h', 'toNat', 'Int', 'toBytes', 'toInt',
        'BitVec', 'ofNat', 'UInt64', 'List', 'UInt8', 'the', 'rip'}


def kebab(s):
    s = re.sub(r'(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])', '-', s)
    return re.sub(r'[^a-z0-9]+', '-', s.replace('_', '-').lower()).strip('-')


def case_id(mod, thm, kind, old=None, new=None):
    t = thm.split('.')[2:]
    out = f"{kebab(mod.split('/')[1])}-{kebab('-'.join(t))}-{'control' if kind == 'control' else 'statement'}"
    if kind != 'control':
        a, b = re.findall(r'[A-Za-z0-9]+', old), re.findall(r'[A-Za-z0-9]+', new)
        rem, add = list(a), list(b)
        for x in a:
            if x in add:
                add.remove(x)
                rem.remove(x)
        first = next((x for x in a if x not in STOP and not x.isdigit()), '')
        r, d = '-'.join(rem[:3]) or 'none', '-'.join(add[:3]) or 'none'
        out += '-' + kebab(f'{first}-{r}-to-{d}' if first else f'{r}-to-{d}')
    return re.sub(r'-+', '-', out)[:120].strip('-')

def stmt_of(path, thm):
    s = open(os.path.join(L, path)).read()
    # the declaring line has the full name without the namespace of its block: the longest suffix that occurs
    parts = thm.split('.')
    decl = next(('.'.join(parts[k:]) for k in range(len(parts)) if 'theorem ' + '.'.join(parts[k:]) + ' ' in s), thm)
    i = s.index(f'theorem {decl} ')
    j = s.find('\ntheorem ', i + 1)
    for t in ('\nend ', '\nexample', '\n/--', '\ndef '):
        k = s.find(t, i + 1)
        if k != -1 and (j == -1 or k < j):
            j = k
    return s[i:j]


def case(mod, thm, old=None, new=None):
    if old is None:
        return dict(id=case_id(mod, thm, 'control'), module=mod, theorem=thm, kind='control')
    body = stmt_of(mod, thm)
    assert body.count(old) == 1, (thm, body.count(old))
    return dict(id=case_id(mod, thm, 'stmt', old, new), module=mod, theorem=thm, kind='stmt', old=old, new=new)


C = []
for T in DEC:
    N = int(re.search(r'\(hlen : s\.regs\.rcx = (\d+)\)', stmt_of(f'Prysm/{T}/GeneratedDecodeAccept.lean', f'Prysm.{T}.Decode.generated_accept')).group(1))
    C.append(case(f'Prysm/{T}/DecodeSpec.lean', f'Prysm.{T}.Decode.accept_spec'))
    C.append(case(f'Prysm/{T}/GeneratedDecodeAccept.lean', f'Prysm.{T}.Decode.generated_accept',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
    C.append(case(f'Prysm/{T}/GeneratedDecodeAccept.lean', f'Prysm.{T}.Decode.generated_reject',
                  'st.data.regs.rax = e0', 'st.data.regs.rax = e1'))
    C.append(case(f'Prysm/{T}/DecodeSpec.lean', f'Prysm.{T}.Decode.accept_spec',
                  '(hlen : s.regs.rcx.toNat = bsA.size)', '(hlen : s.regs.rcx.toNat = bsA.size + 1)'))
    C.append(case(f'Prysm/{T}/WitnessGeneratedDecodeAccept.lean', f'Prysm.{T}.Witness.GeneratedDecodeAccept.runs',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
for T in ENC:
    sp = stmt_of(f'Prysm/{T}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{T}.Encode.generated_fast_spec')
    n = int(re.search(r'\(hcap : s\.regs\.rcx\.toNat \+ (\d+) ≤ s\.regs\.rdi\.toNat\)', sp).group(1))
    wt = stmt_of(f'Prysm/{T}/WitnessGeneratedEncodeFastPath.lean', f'Prysm.{T}.Witness.GeneratedEncodeFastPath.runs_empty')
    rax = re.search(r'st\.data\.regs\.rax = (0x[0-9a-f]+)', wt).group(1)
    C.append(case(f'Prysm/{T}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{T}.Encode.generated_fast_spec'))
    C.append(case(f'Prysm/{T}/GeneratedEncodeFastPath.lean', f'Prysm.{T}.Encode.generated_fast',
                  'st.data.regs.rax = s.regs.rbx', 'st.data.regs.rax = s.regs.rcx'))
    C.append(case(f'Prysm/{T}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{T}.Encode.generated_fast_spec',
                  f'(hcap : s.regs.rcx.toNat + {n} ≤ s.regs.rdi.toNat)', f'(hcap : s.regs.rcx.toNat + {n - 8} ≤ s.regs.rdi.toNat)'))
    C.append(case(f'Prysm/{T}/WitnessGeneratedEncodeFastPath.lean', f'Prysm.{T}.Witness.GeneratedEncodeFastPath.runs_empty',
                  f'st.data.regs.rax = {rax}', 'st.data.regs.rax = 0x8'))
json.dump(C, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(len(C), sum(1 for c in C if c['kind'] == 'control'))
