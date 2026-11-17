"""Write <out>/Prysm/<GoTypeName>/Spec.lean, the spec bridge of each type
(for a field list: SszValue structure, encoding, serialize, roundtrip,
accepts-iff-size, spec reject; codec equality with the checker Desc where a Desc-checker record exists).
The types are the rows of gen/generator/types.tsv with the companion `spec`.
usage: python3 -I -B flat_types_spec.py <out dir>"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'generator'))
import types_table  # noqa: E402

# The fields of the types of the table. `spec_entry` stops with a message for a table type without an entry.
SPEC_TYPES = {  # Go type name: (fields [(name, 'u'|'b', n)], checker (lean name, names) or None)
 'DepositRequest': ([('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                     ('signature', 'b', 96), ('index', 'u', 8)], ('checkerDesc', None)),
 'BuilderDepositRequest': ([('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                            ('signature', 'b', 96)], None),
 'BeaconBlocksByRangeRequest': ([('startSlot', 'u', 8), ('count', 'u', 8), ('step', 'u', 8)], None),
 'BlobSidecarsByRangeRequest': ([('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'ExecutionPayloadEnvelopesByRangeRequest': ([('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'PartialDataColumnGroupID': ([('beaconBlockRoot', 'b', 32), ('slot', 'u', 8)], None),
 'ValidatorIdentity': ([('index', 'u', 8), ('pubkey', 'b', 48), ('activationEpoch', 'u', 8)], None),
 'BuilderPreferences': ([('maxExecutionPayment', 'u', 8)], None),
 'BeaconBlockHeader': ([('slot', 'u', 8), ('proposer', 'u', 8), ('parent', 'b', 32), ('state', 'b', 32), ('body', 'b', 32)],
                       ('checkerDesc', None)),
 'Eth1Data': ([('depositRoot', 'b', 32), ('depositCount', 'u', 8), ('blockHash', 'b', 32)], ('checkerDesc', None)),
 'BlobIdentifier': ([('blockRoot', 'b', 32), ('index', 'u', 8)], ('checkerDesc', None)),
 'DepositMessage': ([('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8)], ('checkerDesc', None)),
 'Deposit_Data': ([('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8), ('signature', 'b', 96)],
                  ('checkerDesc', None)),
 'SyncCommitteeMessage': ([('slot', 'u', 8), ('blockRoot', 'b', 32), ('validatorIndex', 'u', 8), ('signature', 'b', 96)],
                          ('checkerDesc', None)),
 'PendingConsolidation': ([('sourceIndex', 'u', 8), ('targetIndex', 'u', 8)], ('checkerDesc', None)),
 'PendingDeposit': ([('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8), ('signature', 'b', 96),
                     ('slot', 'u', 8)], ('checkerDesc', None)),
 'HistoricalSummary': ([('blockSummaryRoot', 'b', 32), ('stateSummaryRoot', 'b', 32)], ('checkerDesc', None)),
 'SigningData': ([('objectRoot', 'b', 32), ('domain', 'b', 32)], ('checkerDesc', None)),
 'SyncAggregatorSelectionData': ([('slot', 'u', 8), ('subcommitteeIndex', 'u', 8)], ('checkerDesc', None)),
 'ValidatorBalance': ([('index', 'u', 8), ('balance', 'u', 8)], ('checkerDesc', None)),
 'VoluntaryExit': ([('epoch', 'u', 8), ('validatorIndex', 'u', 8)], ('checkerDesc', None)),
 'PendingPartialWithdrawal': ([('index', 'u', 8), ('amount', 'u', 8), ('withdrawableEpoch', 'u', 8)], ('checkerDesc', None)),
}
# The source of the hand `Desc` (SpecDescription.lean) of each type of SPEC_TYPES: consensus-specs or the Prysm proto
# definition. `desc_from_consensus_specs` stops with a message for a type in neither set.
DESC_FROM_CONSENSUS_SPECS = {'BeaconBlockHeader', 'Eth1Data', 'BlobIdentifier', 'DepositMessage', 'Deposit_Data',
                             'SyncCommitteeMessage', 'PendingConsolidation', 'PendingDeposit', 'HistoricalSummary',
                             'SigningData', 'SyncAggregatorSelectionData', 'VoluntaryExit', 'PendingPartialWithdrawal'}
DESC_FROM_PRYSM_PROTO = {'DepositRequest', 'BuilderDepositRequest', 'BeaconBlocksByRangeRequest',
                         'BlobSidecarsByRangeRequest', 'ExecutionPayloadEnvelopesByRangeRequest',
                         'PartialDataColumnGroupID', 'ValidatorIdentity', 'BuilderPreferences', 'ValidatorBalance'}


def desc_from_consensus_specs(X):
    """True if the hand `Desc` of `X` is written from consensus-specs, False if from the Prysm proto definition."""
    if X in DESC_FROM_CONSENSUS_SPECS and X not in DESC_FROM_PRYSM_PROTO:
        return True
    if X in DESC_FROM_PRYSM_PROTO and X not in DESC_FROM_CONSENSUS_SPECS:
        return False
    sys.exit(f'flat_types_spec: {X} must be in exactly one of DESC_FROM_CONSENSUS_SPECS and DESC_FROM_PRYSM_PROTO '
             'of gen/flat-types/flat_types_spec.py (the source of its hand Desc)')


def with_code_imports(text, X):
    """`text` with an import of `Prysm.<T>.Code` after its last import line, for `X` and for each type `T` whose code
    constants the text names (`Prysm.<T>.Code.<name>`) and that the text does not import yet."""
    import re
    ts = [X] + sorted(set(re.findall(r'\bPrysm\.(\w+)\.Code\.\w', text)) - {X})
    lines = text.split('\n')
    last = max(i for i, l in enumerate(lines) if l.startswith('import '))
    new = [f'import Prysm.{t}.Code' for t in ts if f'import Prysm.{t}.Code' not in lines]
    return '\n'.join(lines[:last + 1] + new + lines[last + 1:])


def kind(f):
    return '.uint 8' if f[1] == 'u' else f'.byteVector {f[2]}'


def emit(X, ty, fs, chk):
    value_type, encode_name = 'SszValue', 'SszValue.encode'
    D = 'desc'
    N = sum(f[2] for f in fs)
    us = [f for f in fs if f[1] == 'u']
    offs, o = [], 0
    for f in fs:
        offs.append(o)
        o += f[2]
    L = []
    w = L.append
    w('import Spec.TestScalars')
    w('import Spec.DeserializeOfSerialize')
    w(f'import Prysm.{X}.SpecDescription')
    if chk:
        w(f'import Prysm.{X}.SpecChecker')
    w('')
    w('/-!')
    w(f'# Spec bridge for the Prysm `{ty}`')
    w('')
    w('Written by `gen/flat-types/flat_types_spec.py`.')
    if desc_from_consensus_specs(X):
        w(f'`{D}` (`Prysm/{X}/SpecDescription.lean`) is the independent hand `Desc`, written from consensus-specs.')
    else:
        w(f'`{D}` (`Prysm/{X}/SpecDescription.lean`) is the hand `Desc`, written from the Prysm proto definition.')
        w('It has the same source as the Desc producer, so it is not an independent specification.')
    if chk:
        w(f'`{chk[0]}` (`Prysm/{X}/SpecChecker.lean`, rendered by `gen/checks/desc_to_lean.py`) is the Desc checker\'s Desc of the type')
        w('(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/evidence/`).')
    else:
        w('No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.')
    w(f'`{value_type}` is the SSZ content of a Go `{ty}`.')
    w('-/')
    w('')
    w(f'namespace Prysm.{X}')
    w('open EthLib.Serialization.Ssz')
    w('open Spec hiding readUint_lt')
    w('')
    w(f'theorem {D}_kinds : {D} = .container [{", ".join(chr(34) + nm + chr(34) for nm in descnames[X])}]')
    w(f'      [{", ".join(kind(f) for f in fs)}] := rfl')
    w('')
    w(f'theorem {D}_wellFormed : {D}.wellFormed = .ok () := by rfl')
    w(f'theorem {D}_fixedSize : {D}.fixedSize = some {N} := by rfl')
    w('')
    if chk:
        w('/-- EthLib\'s `serialize` ignores container names. -/')
        w(f'theorem {D}_serialize_checker (v : Value) : serialize {D} v = serialize {chk[0]} v := by')
        w(f'  unfold {D} {chk[0]}')
        w('  cases v <;> (try simp only [serialize, serializeStruct]) <;> rfl')
        w('')
    w(f'/-- The SSZ content of a Go `{ty}`. -/')
    w(f'structure {value_type} where')
    for f in fs:
        w(f'  {f[0]} : {"UInt64" if f[1] == "u" else f"Vector UInt8 {f[2]}"}')
    w('')
    vals = ', '.join(f'.uint g.{f[0]}.toNat' if f[1] == 'u' else f'.bytes g.{f[0]}.toArray' for f in fs)
    w(f'def {value_type}.toValue (g : {value_type}) : Value :=')
    w(f'  .seq [{vals}]')
    w('')
    enc = ' ++ '.join(f'uintBytes 8 g.{f[0]}.toNat' if f[1] == 'u' else f'g.{f[0]}.toArray' for f in fs)
    w(f'def {encode_name} (g : {value_type}) : Array UInt8 :=')
    w(f'  {enc}')
    w('')
    w(f'theorem SszValue.encode_size (g : {value_type}) : ({encode_name} g).size = {N} := by')
    w(f'  simp [{encode_name}, Spec.uintBytes_size]')
    w('')
    lt = '; '.join(f'have := g.{f[0]}.toNat_lt' for f in us)
    w(f'theorem SszValue.toValue_fits (g : {value_type}) : Value.fits {D} g.toValue = true := by')
    w(f'  {lt}')
    w(f'  simp only [{D}, {value_type}.toValue, Value.fits, Value.fieldsFit] at *')
    w('  simp; omega')
    w('')
    n = len(fs)
    a = [f'a{i}' for i in range(n)]
    b = [f'b{i}' for i in range(n)]
    w(f'theorem SszValue.toValue_injective (g h : {value_type}) (e : g.toValue = h.toValue) : g = h := by')
    w(f'  obtain ⟨{", ".join(a)}⟩ := g; obtain ⟨{", ".join(b)}⟩ := h')
    w(f'  simp only [{value_type}.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,')
    w('    and_true] at e')
    inj = lambda i: (f'UInt64.toNat_inj.mp e{i}' if fs[i][1] == 'u' else f'Vector.toArray_inj.mp e{i}')
    if n == 1:
        w(f'  rw [{inj(0).replace("e0", "e")}]')
    else:
        w(f'  obtain ⟨{", ".join(f"e{i}" for i in range(n))}⟩ := e')
        w(f'  rw [{", ".join(inj(i) for i in range(n))}]')
    w('')
    w(f'theorem SszValue.toValue_surjective\' (v : Value) (h : Value.fits {D} v = true) : ∃ g : {value_type}, g.toValue = v := by')
    w('  obtain ⟨vs, rfl, hf⟩ := fits_container h')
    w('  have hl := fieldsFit_length hf')
    w('  match vs, hl with')
    w(f'  | [{", ".join(f"v{i}" for i in range(n))}], _ =>')
    w('    simp only [fieldsFit_cons] at hf')
    w(f'    obtain ⟨{", ".join(f"h{i}" for i in range(n))}, -⟩ := hf')
    for i, f in enumerate(fs):
        if f[1] == 'u':
            w(f'    obtain ⟨a{i}, rfl, ha{i}⟩ := fits_uint h{i}')
        else:
            w(f'    obtain ⟨a{i}, rfl, ha{i}⟩ : ∃ d, v{i} = .bytes d ∧ d.size = {f[2]} := by')
            w(f'      cases v{i} <;> simp [Value.fits] at h{i} ⊢; exact h{i}')
    uh = ' '.join(f'ha{i}' for i, f in enumerate(fs) if f[1] == 'u')
    w(f'    simp only [Nat.reduceMul, Nat.reducePow] at {uh}')
    mk = ', '.join(f'UInt64.ofNat a{i}' if f[1] == 'u' else f'⟨a{i}, ha{i}⟩' for i, f in enumerate(fs))
    mods = ', '.join(f'Nat.mod_eq_of_lt ha{i}' for i, f in enumerate(fs) if f[1] == 'u')
    w(f'    exact ⟨⟨{mk}⟩,')
    w(f'      by simp [{value_type}.toValue, {mods}]⟩')
    w('')
    pat = ', '.join(f'a{i}' if f[1] == 'u' else f'⟨r{i}, hr{i}⟩' for i, f in enumerate(fs))
    hrs = ''.join(f', hr{i}' for i, f in enumerate(fs) if f[1] == 'b')
    lt2 = '; '.join(f'have := a{i}.toNat_lt' for i, f in enumerate(fs) if f[1] == 'u')
    w(f'theorem SszValue.serialize_eq (g : {value_type}) : serialize {D} g.toValue = .ok ({encode_name} g) := by')
    w(f'  obtain ⟨{pat}⟩ := g')
    w(f'  {lt2}')
    w(f'  simp only [{D}, {value_type}.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk{hrs}]')
    w('  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,')
    w(f'    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, {encode_name},')
    w('    Desc.fieldsFixedSize, Array.append_assoc]')
    w('')
    w('/-- **Spec roundtrip.** -/')
    w(f'theorem SszValue.roundtrip (g : {value_type}) : deserialize {D} ({encode_name} g) = .ok g.toValue :=')
    w(f'  deserialize_encoding (G := {value_type}) (toV := {value_type}.toValue) (enc := {encode_name}) {D}_wellFormed SszValue.serialize_eq')
    w(f'    SszValue.toValue_fits g')
    w('')
    w(f'theorem SszValue.accepted_is_encoding {{bs : Array UInt8}} {{v : Value}} (h : deserialize {D} bs = .ok v) :')
    w(f'    ∃ g : {value_type}, v = g.toValue ∧ bs = {encode_name} g :=')
    w(f'  accepted_input_is_encoding (G := {value_type}) (toV := {value_type}.toValue) (enc := {encode_name}) {D}_wellFormed SszValue.serialize_eq')
    w(f'    SszValue.toValue_surjective\' h')
    w('')
    w(f'/-- **EthLib accepts exactly the {N}-byte inputs.** -/')
    w(f'theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize {D} bs = .ok v) ↔ bs.size = {N} := by')
    w('  constructor')
    w('  · rintro ⟨v, hd⟩')
    w(f'    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd')
    w(f'    rw [hb]; exact SszValue.encode_size g')
    w('  · intro h')
    rs = []
    for i, f in enumerate(fs):
        if f[1] == 'u':
            w(f'    have r{i} := readUint_lt bs {offs[i]} 8')
            rs.append(f'r{i}')
    w(f'    simp only [Nat.reducePow, Nat.reduceMul] at {" ".join(rs)}')
    gs = ', '.join(f'UInt64.ofNat (readUint bs {offs[i]} 8)' if f[1] == 'u'
                   else f'⟨bs.extract {offs[i]} {offs[i] + f[2]}, by simp; omega⟩' for i, f in enumerate(fs))
    w(f'    let g : {value_type} := ⟨{gs}⟩')
    w(f'    have e : bs = {encode_name} g := by')
    s1 = ', '.join([f'UInt64.toNat_ofNat_of_lt\' r{i}' for i, f in enumerate(fs) if f[1] == 'u']
                   + [f'uintBytes_readUint_slice bs {offs[i]} 8 (by omega)' for i, f in enumerate(fs) if f[1] == 'u'])
    w(f'      simp only [g, {encode_name}, {s1}]')
    t = 'try ' if n == 1 else ''   # one field: no append to merge (BuilderPreferences)
    w(f'      {t}simp only [Nat.zero_add, Nat.reduceAdd]')
    w(f'      {t}simp (config := {{decide := true}}) only [Array.extract_append_extract, Nat.min_def, Nat.max_def, ↓reduceIte]')
    w('      rw [← h]; simp')
    w('    rw [e]')
    w(f'    exact ⟨_, SszValue.roundtrip g⟩')
    w('')
    w(f'/-- `len(buf) ≠ {N}`: EthLib rejects. -/')
    w(f'theorem SszValue.spec_rejects (bs : Array UInt8) (h : bs.size ≠ {N}) : ∃ e, deserialize {D} bs = .error e := by')
    w(f'  cases hd : deserialize {D} bs with')
    w('  | error e => exact ⟨e, rfl⟩')
    w(f'  | ok v => exact absurd ((SszValue.spec_accepts_iff bs).mp ⟨v, hd⟩) h')
    w('')
    if chk:
        c = chk[0]
        w('/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/')
        w('')
        w(f'theorem checker_wellFormed : {c}.wellFormed = .ok () := by rfl')
        w('')
        w(f'theorem SszValue.serialize_eq_checker (g : {value_type}) : serialize {c} g.toValue = .ok ({encode_name} g) := by')
        w(f'  rw [← {D}_serialize_checker]; exact SszValue.serialize_eq g')
        w('')
        w(f'theorem SszValue.toValue_fits_checker (g : {value_type}) : Value.fits {c} g.toValue = true := by')
        w(f'  {lt}')
        w(f'  simp [{c}, {value_type}.toValue, Value.fits, Value.fieldsFit]; omega')
        w('')
        w(f'theorem SszValue.toValue_surjective_checker (v : Value) (h : Value.fits {c} v = true) :')
        w(f'    ∃ g : {value_type}, g.toValue = v := by')
        w(f'  have h\' : Value.fits {D} v = true := by')
        w(f'    cases v <;> simp_all [{D}, {c}, Value.fits]')
        w(f'  exact SszValue.toValue_surjective\' v h\'')
        w('')
        w('/-- **Codec equality on the accepted inputs**. -/')
        w(f'theorem {D}_deserialize_checker (bs : Array UInt8) (v : Value) :')
        w(f'    deserialize {D} bs = .ok v ↔ deserialize {c} bs = .ok v := by')
        w('  constructor')
        w('  · intro h')
        w(f'    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding h')
        w('    rw [hb]')
        w(f'    exact deserialize_encoding (G := {value_type}) (toV := {value_type}.toValue) (enc := {encode_name}) checker_wellFormed')
        w(f'      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g')
        w('  · intro h')
        w(f'    obtain ⟨g, rfl, hb⟩ := accepted_input_is_encoding (G := {value_type}) (toV := {value_type}.toValue) (enc := {encode_name})')
        w(f'      checker_wellFormed SszValue.serialize_eq_checker SszValue.toValue_surjective_checker h')
        w(f'    rw [hb]; exact SszValue.roundtrip g')
        w('')
    w(f'end Prysm.{X}')
    return '\n'.join(L) + '\n'


descnames = {
 'DepositRequest': ['pubkey', 'withdrawal_credentials', 'amount', 'signature', 'index'],
 'BuilderDepositRequest': ['pubkey', 'withdrawal_credentials', 'amount', 'signature'],
 'BeaconBlocksByRangeRequest': ['start_slot', 'count', 'step'], 'BlobSidecarsByRangeRequest': ['start_slot', 'count'], 'ExecutionPayloadEnvelopesByRangeRequest': ['start_slot', 'count'],
 'PartialDataColumnGroupID': ['beacon_block_root', 'slot'], 'ValidatorIdentity': ['index', 'pubkey', 'activation_epoch'],
 'BuilderPreferences': ['max_execution_payment'],
 'BeaconBlockHeader': ['slot', 'proposer_index', 'parent_root', 'state_root', 'body_root'],
 'Eth1Data': ['deposit_root', 'deposit_count', 'block_hash'], 'BlobIdentifier': ['block_root', 'index'],
 'DepositMessage': ['pubkey', 'withdrawal_credentials', 'amount'],
 'Deposit_Data': ['pubkey', 'withdrawal_credentials', 'amount', 'signature'],
 'SyncCommitteeMessage': ['slot', 'beacon_block_root', 'validator_index', 'signature'],
 'PendingConsolidation': ['source_index', 'target_index'],
 'PendingDeposit': ['pubkey', 'withdrawal_credentials', 'amount', 'signature', 'slot'],
 'HistoricalSummary': ['block_summary_root', 'state_summary_root'], 'SigningData': ['object_root', 'domain'],
 'SyncAggregatorSelectionData': ['slot', 'subcommittee_index'], 'ValidatorBalance': ['index', 'balance'],
 'VoluntaryExit': ['epoch', 'validator_index'], 'PendingPartialWithdrawal': ['validator_index', 'amount', 'withdrawable_epoch'],
}


def spec_entry(X, tool):
    """(Go type with package, fields, checker) of the table type `X`. `tool` names the program in the message."""
    if X not in SPEC_TYPES or X not in descnames:
        sys.exit(f'{tool}: {X} is a type of gen/generator/types.tsv without an entry in SPEC_TYPES and descnames '
                 'of gen/flat-types/flat_types_spec.py')
    fs, chk = SPEC_TYPES[X]
    return f'{types_table.package_of(X)}.{X}', fs, chk


if __name__ == '__main__':
    out = sys.argv[1]
    for X in types_table.types_with('spec'):
        ty, fs, chk = spec_entry(X, 'flat_types_spec')
        os.makedirs(os.path.join(out, 'Prysm', X), exist_ok=True)
        open(os.path.join(out, 'Prysm', X, 'Spec.lean'), 'w').write(emit(X, ty, fs, chk))
        print(X)
