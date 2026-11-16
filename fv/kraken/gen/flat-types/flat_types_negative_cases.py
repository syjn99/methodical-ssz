"""Write the negative cases of the flat types (gen/checks/negative-cases/negative-cases-flat-types.json) for gen/checks/negative.py.
Per decoder type: accept_spec control; mutants of the generated accept theorem (post rax), the generated size-reject
theorem (post rax), accept_spec (hlen + 1), the accept witness (post rax). Per encoder type: spec control; mutants of the
generated fast-path theorem (post rax), the spec corollary (hcap weakened by 8), the witness (post rax)."""
import json, os, re, sys
LEAN_DIR = sys.argv[1]   # fv/kraken/lean
DECODER_CASE_TYPES = ['DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest', 'BlobSidecarsByRangeRequest',
       'ExecutionPayloadEnvelopesByRangeRequest', 'PartialDataColumnGroupID', 'ValidatorIdentity']
ENCODER_CASE_TYPES = ['BeaconBlocksByRangeRequest', 'BuilderDepositRequest', 'BuilderPreferences', 'BlobSidecarsByRangeRequest',
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

def statement_of(path, thm):
    s = open(os.path.join(LEAN_DIR, path)).read()
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
    body = statement_of(mod, thm)
    assert body.count(old) == 1, (thm, body.count(old))
    return dict(id=case_id(mod, thm, 'statement', old, new), module=mod, theorem=thm, kind='statement', old=old, new=new)


CASES = []
for type_name in DECODER_CASE_TYPES:
    N = int(re.search(r'\(hlen : s\.regs\.rcx = (\d+)\)', statement_of(f'Prysm/{type_name}/GeneratedDecodeAccept.lean', f'Prysm.{type_name}.Decode.generated_accept')).group(1))
    CASES.append(case(f'Prysm/{type_name}/DecodeSpec.lean', f'Prysm.{type_name}.Decode.accept_spec'))
    CASES.append(case(f'Prysm/{type_name}/GeneratedDecodeAccept.lean', f'Prysm.{type_name}.Decode.generated_accept',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
    CASES.append(case(f'Prysm/{type_name}/GeneratedDecodeAccept.lean', f'Prysm.{type_name}.Decode.generated_reject',
                  'st.data.regs.rax = e0', 'st.data.regs.rax = e1'))
    CASES.append(case(f'Prysm/{type_name}/DecodeSpec.lean', f'Prysm.{type_name}.Decode.accept_spec',
                  '(hlen : s.regs.rcx.toNat = bsA.size)', '(hlen : s.regs.rcx.toNat = bsA.size + 1)'))
    CASES.append(case(f'Prysm/{type_name}/WitnessGeneratedDecodeAccept.lean', f'Prysm.{type_name}.Witness.GeneratedDecodeAccept.runs',
                  'st.data.regs.rax = 0 ∧', 'st.data.regs.rax = 1 ∧'))
for type_name in ENCODER_CASE_TYPES:
    sp = statement_of(f'Prysm/{type_name}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{type_name}.Encode.generated_fast_spec')
    n = int(re.search(r'\(hcap : s\.regs\.rcx\.toNat \+ (\d+) ≤ s\.regs\.rdi\.toNat\)', sp).group(1))
    wt = statement_of(f'Prysm/{type_name}/WitnessGeneratedEncodeFastPath.lean', f'Prysm.{type_name}.Witness.GeneratedEncodeFastPath.runs_empty')
    rax = re.search(r'st\.data\.regs\.rax = (0x[0-9a-f]+)', wt).group(1)
    CASES.append(case(f'Prysm/{type_name}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{type_name}.Encode.generated_fast_spec'))
    CASES.append(case(f'Prysm/{type_name}/GeneratedEncodeFastPath.lean', f'Prysm.{type_name}.Encode.generated_fast',
                  'st.data.regs.rax = s.regs.rbx', 'st.data.regs.rax = s.regs.rcx'))
    CASES.append(case(f'Prysm/{type_name}/GeneratedEncodeFastPathSpec.lean', f'Prysm.{type_name}.Encode.generated_fast_spec',
                  f'(hcap : s.regs.rcx.toNat + {n} ≤ s.regs.rdi.toNat)', f'(hcap : s.regs.rcx.toNat + {n - 8} ≤ s.regs.rdi.toNat)'))
    CASES.append(case(f'Prysm/{type_name}/WitnessGeneratedEncodeFastPath.lean', f'Prysm.{type_name}.Witness.GeneratedEncodeFastPath.runs_empty',
                  f'st.data.regs.rax = {rax}', 'st.data.regs.rax = 0x8'))
json.dump(CASES, open(sys.argv[2], 'w'), indent=1, ensure_ascii=False)
print(len(CASES), sum(1 for c in CASES if c['kind'] == 'control'))
