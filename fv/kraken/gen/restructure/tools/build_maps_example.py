"""EXAMPLE for one step: the map builder of the step attestation-data (base commit 197e2a21).

It writes files.tsv, names.tsv, declared.txt and protect.txt of maps/attestation-data/.
It does not apply to other steps as it is. For a new step, copy it, then change FILES, NAMESPACE_ROWS,
OPEN_ROWS, TYPE_NAMESPACES and RENAMES, and the old namespace filter in the main loop (`E2eAd.`, `E2e.`).
The generic parts are the namespace rule (ns_map), the rows of generated declarations (`.mk`, fields, `.eq_1`),
the uniqueness asserts, and declared.txt.

usage (from the repository root):
  python3 -I -B fv/kraken/gen/restructure/tools/build_maps_example.py <dump.tsv> <out dir> <protect.txt>

  <dump.tsv>     declaration dump of the base tree, written by dump_all.lean (module, name, kind, internal flag)
  <out dir>      directory for the four map files (created if it does not exist)
  <protect.txt>  the protect.txt to copy, for example fv/kraken/gen/restructure/maps/checkpoint-and-epoch/protect.txt

Check: with the dump of 197e2a21 the output is equal to the committed maps/attestation-data/ files.
The builder stops when a new name already exists in the dump, or when two rows get the same old or new name.
"""
import sys, re, collections, os, shutil
if len(sys.argv) != 4:
    sys.exit(__doc__)
DUMP, OUT_DIR, PROTECT_FILE = sys.argv[1:4]
LEAN_DIR = 'fv/kraken/lean/'
DIR_ATTESTATION_DATA, DIR_SLOT, DIR_COMMITTEE_INDEX, DIR_CHECKPOINT, DIR_ELF_DATA = 'Prysm/AttestationData/', 'Prysm/Slot/', 'Prysm/CommitteeIndex/', 'Prysm/Checkpoint/', 'Prysm/ElfData/'
FILES = [
 ('E2eAd/Code.lean', DIR_ATTESTATION_DATA + 'Code.lean', 'program constants of the AttestationData link set: AttestationData UnmarshalSSZ, MarshalSSZTo and SizeSSZ, the Slot and CommitteeIndex UnmarshalSSZ, and the labels of the Checkpoint callees (shared with Slot and CommitteeIndex, needs a split)'),
 ('E2eAd/Include.lean', DIR_ELF_DATA + 'AttestationDataReader.lean', 'the command ad_data_include that reads the data files of the AttestationData link set (the Checkpoint and Epoch reader with the set prefix ad)'),
 ('E2eAd/Data.lean', DIR_ELF_DATA + 'AttestationData.lean', 'ELF data of the link set prysm/go1.26.10/e2e/ad/link: the Checkpoint abi.Type word and the four field error format strings'),
 ('E2eAd/Layout.lean', DIR_ATTESTATION_DATA + 'Layout.lean', 'generated Go struct layout of v1alpha1.AttestationData (field offsets and sizes)'),
 ('E2eAd/SpecChecker.lean', DIR_ATTESTATION_DATA + 'SpecChecker.lean', 'generated description of v1alpha1.AttestationData for the description checker'),
 ('E2eAd/Spec.lean', DIR_ATTESTATION_DATA + 'Spec.lean', 'EthLib description of v1alpha1.AttestationData, the SSZ value structure and the bridge lemmas; also the equality with the checker description (mixed module, main role Spec)'),
 ('E2eAd/Prims.lean', DIR_SLOT + 'DecodeAccept.lean', 'decoder accept path of the hand-written primitives.Slot and primitives.CommitteeIndex UnmarshalSSZ and their function specifications (shared with CommitteeIndex, needs a split)'),
 ('E2eAd/AdHead.lean', DIR_ATTESTATION_DATA + 'DecodeAcceptHead.lean', 'decoder accept path, part 1: the length check and the Slot and CommitteeIndex calls'),
 ('E2eAd/AdRoot.lean', DIR_ATTESTATION_DATA + 'DecodeAcceptBlockRoot.lean', 'decoder accept path, part 2: the BeaconBlockRoot slice (makeslice and memmove)'),
 ('E2eAd/AdSrc.lean', DIR_ATTESTATION_DATA + 'DecodeAcceptSource.lean', 'decoder accept path, part 3: the new Source object and the Checkpoint call, and the callee frame lemmas'),
 ('E2eAd/AdTgt.lean', DIR_ATTESTATION_DATA + 'DecodeAcceptTarget.lean', 'decoder accept path, part 4: the new Target object, the Checkpoint call and the return'),
 ('E2eAd/AdAccept.lean', DIR_ATTESTATION_DATA + 'DecodeAccept.lean', 'decoder accept path: the composition of the four parts'),
 ('E2eAd/AdReject.lean', DIR_ATTESTATION_DATA + 'DecodeRejectSize.lean', 'decoder size reject, and the four error wraps that no 128-byte input reaches (mixed module, main role size reject)'),
 ('E2eAd/AdSpecK.lean', DIR_ATTESTATION_DATA + 'DecodeSpec.lean', 'decoder against EthLib: accept, size reject and reject completeness'),
 ('E2eAd/BumpNew72.lean', DIR_ATTESTATION_DATA + 'WitnessBumpAllocator.lean', 'bump allocator model of runtime.newobject for one 72-byte object, for the AttestationData witnesses only (no role of the table fits)'),
 ('E2eAd/BumpNew72.S', DIR_ATTESTATION_DATA + 'BumpNew72.S', 'assembly of the 72-byte bump newobject model (file name kept: the name of its Program constant)'),
 ('E2eAd/WitAdA.lean', DIR_ATTESTATION_DATA + 'WitnessDecodeAccept.lean', 'witness of the decoder accept theorem'),
 ('E2eAd/WitAdR.lean', DIR_ATTESTATION_DATA + 'WitnessDecodeRejectSize.lean', 'witness of the decoder size reject theorem'),
 ('E2eAd/WitSl.lean', DIR_SLOT + 'WitnessDecodeAccept.lean', 'witness of the Slot decoder accept theorem and of its function specification'),
 ('E2eAd/WitCi.lean', DIR_COMMITTEE_INDEX + 'WitnessDecodeAccept.lean', 'witness of the CommitteeIndex decoder accept theorem and of its function specification'),
 ('E2eAd/CpSpecs.lean', DIR_CHECKPOINT + 'FunctionSpecsAsNestedField.lean', 'function specifications of the Checkpoint decoder and encoder at their labels, for a caller that holds Checkpoint as a nested field'),
 ('E2eAd/WitCpSpecs.lean', DIR_CHECKPOINT + 'WitnessDecodeFunctionSpecAsNestedField.lean', 'the Checkpoint decoder function specification holds on the Checkpoint decoder witness host'),
 ('E2eAd/WitCpMS.lean', DIR_CHECKPOINT + 'WitnessEncodeFunctionSpecAsNestedField.lean', 'the Checkpoint encoder function specification holds on the Checkpoint encoder witness host'),
]
NEW_MODULE = {o[:-5].replace('/', '.'): n[:-5].replace('/', '.') for o, n, _ in FILES if o.endswith('.lean')}
ATTESTATION_DATA, SLOT, COMMITTEE_INDEX, CHECKPOINT = 'Prysm.AttestationData', 'Prysm.Slot', 'Prysm.CommitteeIndex', 'Prysm.Checkpoint'
NAMESPACE_ROWS = [  # old namespace, new namespace, scope (new module prefix or MODULE#N), whole|part
 ('E2eAd', ATTESTATION_DATA, ATTESTATION_DATA, 'part'), ('E2e', ATTESTATION_DATA, ATTESTATION_DATA, 'part'),
 ('E2eAd', SLOT, 'Prysm.Slot.DecodeAccept#1', 'part'), ('E2eAd', COMMITTEE_INDEX, 'Prysm.Slot.DecodeAccept#2', 'part'),
 ('E2eAd', CHECKPOINT, CHECKPOINT, 'part'),
 ('E2eAd.Code', ATTESTATION_DATA + '.Code', ATTESTATION_DATA, 'whole'),
 ('E2eAd.Data', 'ElfData.AttestationData', 'Prysm.ElfData', 'whole'),
 ('E2eAd.WitAdA', ATTESTATION_DATA + '.Witness.DecodeAccept', ATTESTATION_DATA, 'whole'),
 ('E2eAd.WitAdR', ATTESTATION_DATA + '.Witness.DecodeRejectSize', ATTESTATION_DATA, 'whole'),
 ('E2eAd.WitSl', SLOT + '.Witness.DecodeAccept', SLOT, 'whole'),
 ('E2eAd.WitCi', COMMITTEE_INDEX + '.Witness.DecodeAccept', COMMITTEE_INDEX, 'whole'),
 ('E2eAd.WitCpSpecs', CHECKPOINT + '.Witness.DecodeFunctionSpecAsNestedField', CHECKPOINT, 'whole'),
 ('E2eAd.WitCpMS', CHECKPOINT + '.Witness.EncodeFunctionSpecAsNestedField', CHECKPOINT, 'whole'),
]
OPEN_ROWS = [('E2eAd.Code', ATTESTATION_DATA + '.Code', ATTESTATION_DATA), ('E2eAd.Code', ATTESTATION_DATA + '.Code', SLOT), ('E2eAd.Code', ATTESTATION_DATA + '.Code', COMMITTEE_INDEX),
         ('E2eAd.Code', ATTESTATION_DATA + '.Code', '-'), ('E2eAd.Data', 'ElfData.AttestationData', '*')]
TYPE_NAMESPACES = [ATTESTATION_DATA, SLOT, COMMITTEE_INDEX, CHECKPOINT]
RENAMES = {  # old full name -> new full name (a name not listed takes the namespace rule)
 'E2eAd.Code.AdUnmarshal': ATTESTATION_DATA + '.Code.unmarshalSSZ', 'E2eAd.Code.AdMarshal': ATTESTATION_DATA + '.Code.marshalSSZTo',
 'E2eAd.Code.AdSize': ATTESTATION_DATA + '.Code.sizeSSZ',
 'E2eAd.Code.SlUnmarshal': ATTESTATION_DATA + '.Code.slotUnmarshalSSZ', 'E2eAd.Code.CiUnmarshal': ATTESTATION_DATA + '.Code.committeeIndexUnmarshalSSZ',
 'E2eAd.Code.slLabel': ATTESTATION_DATA + '.Code.slotUnmarshalLabel', 'E2eAd.Code.ciLabel': ATTESTATION_DATA + '.Code.committeeIndexUnmarshalLabel',
 'E2eAd.Code.cpULabel': ATTESTATION_DATA + '.Code.checkpointUnmarshalLabel', 'E2eAd.Code.cpMLabel': ATTESTATION_DATA + '.Code.checkpointMarshalLabel',
 'E2e.adGoFields': ATTESTATION_DATA + '.goFields', 'E2e.adGoSize': ATTESTATION_DATA + '.goSize', 'E2e.adGoAlign': ATTESTATION_DATA + '.goAlign',
 'E2e.adCheckerDesc': ATTESTATION_DATA + '.checkerDesc',
 'E2e.prysmAdDesc': ATTESTATION_DATA + '.desc', 'E2e.PAd': ATTESTATION_DATA + '.SszValue', 'E2e.padEnc': ATTESTATION_DATA + '.SszValue.encode',
 'E2e.pad_enc_size': ATTESTATION_DATA + '.SszValue.enc_size', 'E2e.pad_toValue_fits': ATTESTATION_DATA + '.SszValue.toValue_fits',
 'E2e.pad_toValue_injective': ATTESTATION_DATA + '.SszValue.toValue_injective',
 'E2e.pad_toValue_surjective': ATTESTATION_DATA + '.SszValue.toValue_surjective', "E2e.pad_toValue_surjective'": ATTESTATION_DATA + ".SszValue.toValue_surjective'",
 'E2e.pad_serialize': ATTESTATION_DATA + '.SszValue.serialize_eq', 'E2e.pad_roundtrip': ATTESTATION_DATA + '.SszValue.roundtrip',
 'E2e.pad_accepted_is_enc': ATTESTATION_DATA + '.SszValue.accepted_is_encoding',
 'E2e.pad_serialize_checker': ATTESTATION_DATA + '.SszValue.serialize_eq_checker',
 'E2e.pad_toValue_fits_checker': ATTESTATION_DATA + '.SszValue.toValue_fits_checker',
 'E2e.pad_toValue_surjective_checker': ATTESTATION_DATA + '.SszValue.toValue_surjective_checker',
 'E2e.pad_spec_accepts_iff': ATTESTATION_DATA + '.SszValue.spec_accepts_iff', 'E2e.pad_spec_rejects': ATTESTATION_DATA + '.SszValue.spec_rejects',
 'E2e.adChecker_wellFormed': ATTESTATION_DATA + '.checker_wellFormed',
 'E2e.pcp_toValue_injective': ATTESTATION_DATA + '.checkpoint_toValue_injective', 'E2e.pcp_of_bytes': ATTESTATION_DATA + '.checkpoint_of_bytes',
 'E2e.pcp_toValue_surjective_checker': ATTESTATION_DATA + '.checkpoint_toValue_surjective_checker',
 'E2eAd.sl_unmarshal_accept_main': SLOT + '.Decode.accept', 'E2eAd.SlUAccC': SLOT + '.Decode.accept_function_spec',
 'E2eAd.sl_uacc_holds': SLOT + '.Decode.accept_function_spec_holds',
 'E2eAd.ci_unmarshal_accept_main': COMMITTEE_INDEX + '.Decode.accept', 'E2eAd.CiUAccC': COMMITTEE_INDEX + '.Decode.accept_function_spec',
 'E2eAd.ci_uacc_holds': COMMITTEE_INDEX + '.Decode.accept_function_spec_holds',
 'E2eAd.ad_e2e_accept_main': ATTESTATION_DATA + '.Decode.accept', 'E2eAd.ad_e2e_reject_size_main': ATTESTATION_DATA + '.Decode.reject_size',
 'E2eAd.ad_e2e_slot_err_unreachable': ATTESTATION_DATA + '.Decode.slot_err_unreachable',
 'E2eAd.ad_e2e_ci_err_unreachable': ATTESTATION_DATA + '.Decode.committee_index_err_unreachable',
 'E2eAd.ad_e2e_source_err_unreachable': ATTESTATION_DATA + '.Decode.source_err_unreachable',
 'E2eAd.ad_e2e_target_err_unreachable': ATTESTATION_DATA + '.Decode.target_err_unreachable',
 'E2eAd.ad_e2e_accept_spec_k': ATTESTATION_DATA + '.Decode.accept_spec', 'E2eAd.ad_e2e_reject_size_spec': ATTESTATION_DATA + '.Decode.reject_size_spec',
 'E2eAd.ad_e2e_reject_complete': ATTESTATION_DATA + '.Decode.reject_complete',
 'E2eAd.ad_e2e_head': ATTESTATION_DATA + '.Decode.head', 'E2eAd.ad_e2e_root': ATTESTATION_DATA + '.Decode.block_root',
 'E2eAd.ad_e2e_src': ATTESTATION_DATA + '.Decode.source', 'E2eAd.ad_e2e_tgt': ATTESTATION_DATA + '.Decode.target',
 'E2eAd.adFrame': ATTESTATION_DATA + '.Decode.frame', 'E2eAd.adFrame_length': ATTESTATION_DATA + '.Decode.frame_length',
 'E2eAd.adFrame_sep': ATTESTATION_DATA + '.Decode.frame_sep', 'E2eAd.adFrame_slices': ATTESTATION_DATA + '.Decode.frame_slices',
 'E2eAd.adFrame_lens': ATTESTATION_DATA + '.Decode.frame_lens',
 'E2eAd.CpUAccC': CHECKPOINT + '.Decode.accept_function_spec', 'E2eAd.cp_uacc_holds': CHECKPOINT + '.Decode.accept_function_spec_holds',
 'E2eAd.CpMAccC': CHECKPOINT + '.Encode.fast_path_function_spec', 'E2eAd.cp_macc_holds': CHECKPOINT + '.Encode.fast_path_function_spec_holds',
 'E2eAd.WitAdA.ad_accept_runs': ATTESTATION_DATA + '.Witness.DecodeAccept.runs',
 'E2eAd.WitAdR.ad_reject_runs': ATTESTATION_DATA + '.Witness.DecodeRejectSize.runs',
 'E2eAd.WitSl.sl_accept_runs': SLOT + '.Witness.DecodeAccept.runs', 'E2eAd.WitSl.sl_spec_here': SLOT + '.Witness.DecodeAccept.runs_function_spec',
 'E2eAd.WitSl.sl_wit_mem': SLOT + '.Witness.DecodeAccept.witness_mem',
 'E2eAd.WitCi.ci_accept_runs': COMMITTEE_INDEX + '.Witness.DecodeAccept.runs', 'E2eAd.WitCi.ci_spec_here': COMMITTEE_INDEX + '.Witness.DecodeAccept.runs_function_spec',
 'E2eAd.WitCi.ci_wit_mem': COMMITTEE_INDEX + '.Witness.DecodeAccept.witness_mem',
 'E2eAd.WitCpSpecs.cpu_spec_here': CHECKPOINT + '.Witness.DecodeFunctionSpecAsNestedField.runs_function_spec',
 'E2eAd.WitCpMS.cpm_spec_here': CHECKPOINT + '.Witness.EncodeFunctionSpecAsNestedField.runs_function_spec',
}
for x in ['slot', 'call', 'ret', 'guard', 'lo', 'mm3', 'obj72', 'guard96', 'lo88', 'j3', 's3']:
    RENAMES['E2eAd.ada_' + x] = ATTESTATION_DATA + '.Decode.accept_' + x
for x in ['adCpType', 'adFmtSlot', 'adFmtCi', 'adFmtSource', 'adFmtTarget']:
    for y in (x, x + '_addr'):
        RENAMES['E2eAd.Data.' + y] = 'ElfData.AttestationData.' + y
for s in ['checker', 'eq_hand', 'wellFormed', 'fixedSize', 'serialize_checker', 'deserialize_checker']:
    RENAMES['E2e.prysmAdDesc_' + s] = ATTESTATION_DATA + '.desc_' + s

def ns_map(name, mod):
    new_module = NEW_MODULE[mod]; best = None
    for o, n, scope, _ in NAMESPACE_ROWS:
        if '#' in scope: continue
        if (new_module == scope or new_module.startswith(scope + '.')) and (name == o or name.startswith(o + '.')):
            rank = (len(scope), len(o))
            if best is None or rank > best[2]: best = (o, n, rank)
    if best is None: raise SystemExit('no namespace rule for %s in %s' % (name, mod))
    return best[1] + name[len(best[0]):]

# Main loop: one declaration row for every non-internal declaration of a moved module.
# A name below another moved name (a generated `.mk`, a field, `.eq_1`) follows its parent unless RENAMES names it.
rows, generated_rows = [], []
dump_rows =[l.rstrip('\n').split('\t') for l in open(DUMP)]
moved_old = {n: m for m, n, k, i in dump_rows if m in NEW_MODULE}
old_names = {n for m, n, k, i in dump_rows}
for m, n, k, i in dump_rows:
    if m not in NEW_MODULE or i == '1':
        continue
    if not (n.startswith('E2eAd.') or n.startswith('E2e.')):
        continue
    parts = n.split('.')
    under = next(('.'.join(parts[:j]) for j in range(len(parts) - 1, 0, -1) if '.'.join(parts[:j]) in moved_old), None)
    if under is not None and not n in RENAMES:
        generated_rows.append((n, under, m)); continue
    if n in RENAMES:
        nn = RENAMES[n]
    elif m == 'E2eAd.Prims' or m == 'E2eAd.CpSpecs':
        raise SystemExit('unmapped declaration of a split module: ' + n)
    else:
        nn = ns_map(n, m)
        if '.Code.' in nn: raise SystemExit('unmapped code constant ' + n)
    rows.append((n, nn, NEW_MODULE[m]))
newof = {r[0]: r[1] for r in rows}
for n, under, m in generated_rows:
    while under not in newof:
        under = under.rsplit('.', 1)[0]
    rows.append((n, newof[under] + n[len(under):], NEW_MODULE[m]))
for n in RENAMES:
    assert n in moved_old, n
olds = collections.Counter(r[0] for r in rows); news = collections.Counter(r[1] for r in rows)
assert all(v == 1 for v in olds.values()) and all(v == 1 for v in news.values()), [x for x, v in news.items() if v > 1]
for r in rows:
    assert r[1] not in old_names, ('new name exists in the old tree', r)
rows.sort(key=lambda r: (r[2], r[0]))
os.makedirs(OUT_DIR, exist_ok=True)
with open(f'{OUT_DIR}/files.tsv', 'w') as f:
    f.write('# old path\tnew path\tmeaning (paths are relative to the repository root)\n')
    for o, n, meaning in FILES: f.write(f'{LEAN_DIR}{o}\t{LEAN_DIR}{n}\t{meaning}\n')
with open(f'{OUT_DIR}/names.tsv', 'w') as f:
    f.write('# kind\told name\tnew name\tscope\tfifth column (see ../../README.md section 2)\n')
    f.write('# namespace: old namespace, new namespace, module prefix of the moved modules where the row applies (MODULE#N: the N-th\n')
    f.write('#   top-level namespace block of that module), whole|part\n')
    f.write('# open: old namespace, new namespace, type namespace of the file (- outside every type, * every file), -\n')
    f.write('# type: the namespace of one type; outside it a reference is written with the full name\n')
    f.write('# declaration: old full name, new full name, library, new module\n')
    for o, n, scope, w in NAMESPACE_ROWS: f.write(f'namespace\t{o}\t{n}\t{scope}\t{w}\n')
    for o, n, s in OPEN_ROWS: f.write(f'open\t{o}\t{n}\t{s}\t-\n')
    for t in TYPE_NAMESPACES: f.write(f'type\t{t}\t-\t-\t-\n')
    for o, n, new_module in rows: f.write(f'declaration\t{o}\t{n}\tPrysm\t{new_module}\n')
# declared.txt: names of the base tree that the step does not move and whose last component is a component of a
# moved old name or of the last three components of a moved new name.
components = set()
for o, n, _ in rows:
    components.add(o.split('.')[-1]); components |= set(n.split('.')[len(n.split('.')) - 3:])
GENERATED_COMPONENT = re.compile(r'^(eq_\d+|eq_def|match_\d+(_\d+)?|proof_\d+|mk|rec|recOn|casesOn|noConfusion|noConfusionType|ctorIdx|inj|injEq|sizeOf_spec|_.*)$')
components = {x for x in components if not GENERATED_COMPONENT.match(x)}
namespaces = set()
for name in old_names:
    p = name.split('.')
    for j in range(1, len(p)): namespaces.add('.'.join(p[:j]))
moved_namespaces = {r[0].rsplit('.', 1)[0] for r in rows}
with open(f'{OUT_DIR}/declared.txt', 'w') as f:
    f.write('# Names of the old tree (declarations and namespaces, not moved by this step) whose last component is a\n')
    f.write('# component of a moved name: rename.py resolves short references against them. From a Lean dump.\n')
    out = sorted(x for x in (old_names | namespaces) if x not in moved_old and not any(x.startswith(o + '.') for o in moved_old)
                 and x.split('.')[-1] in components and not x.startswith('_private') and '._' not in x
                 and not ((x.startswith('E2eAd') or x.startswith('E2e.')) and x in moved_namespaces))
    for x in out: f.write(x + '\n')
shutil.copy(PROTECT_FILE, f'{OUT_DIR}/protect.txt')
print(len(rows), 'declaration rows;', len(out), 'declared names')
