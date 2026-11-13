"""Evidence tool (not part of gen/generator): write <out>/Prysm/<GoTypeName>/Spec.lean, the spec bridge of each type
(the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean` generalised to a field list: P structure, encoding, serialize, roundtrip,
accepts-iff-size, spec reject; codec equality with the checker Desc where a Desc-checker record exists).
usage: python3 -I -B flat_types_spec.py <out dir>"""
import sys, os

T = {  # Go type name: (Go type with package, fields [(name, 'u'|'b', n)], checker (lean name, names) or None)
 'DepositRequest': ('v1.DepositRequest', [('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                               ('signature', 'b', 96), ('index', 'u', 8)],
         ('checkerDesc', None)),
 'BuilderDepositRequest': ('v1.BuilderDepositRequest', [('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                                      ('signature', 'b', 96)], None),
 'BeaconBlocksByRangeRequest': ('v1alpha1.BeaconBlocksByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8), ('step', 'u', 8)], None),
 'BlobSidecarsByRangeRequest': ('v1alpha1.BlobSidecarsByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'ExecutionPayloadEnvelopesByRangeRequest': ('v1alpha1.ExecutionPayloadEnvelopesByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'PartialDataColumnGroupID': ('v1alpha1.PartialDataColumnGroupID', [('beaconBlockRoot', 'b', 32), ('slot', 'u', 8)], None),
 'ValidatorIdentity': ('v1alpha1.ValidatorIdentity', [('index', 'u', 8), ('pubkey', 'b', 48), ('activationEpoch', 'u', 8)], None),
 'BuilderPreferences': ('v1alpha1.BuilderPreferences', [('maxExecutionPayment', 'u', 8)], None),
}


def kind(f):
    return '.uint 8' if f[1] == 'u' else f'.byteVector {f[2]}'


def emit(X, ty, fs, chk):
    P, pe = 'SszValue', 'SszValue.encode'
    D = 'desc'
    N = sum(f[2] for f in fs)
    us = [f for f in fs if f[1] == 'u']
    offs, o = [], 0
    for f in fs:
        offs.append(o)
        o += f[2]
    L = []
    w = L.append
    w('import Prysm.Checkpoint.Spec')
    w('import Prysm.Checkpoint.SpecEquivalence')
    w('import Prysm.DepositRequest.SpecDescription')
    if chk:
        w(f'import Prysm.{X}.SpecChecker')
    w('')
    w('/-!')
    w(f'# Spec bridge for the real Prysm `{ty}` (24 flat hold-out types)')
    w('')
    w('Written by the evidence script `flat_types_spec.py` (the text of `Prysm/SyncCommitteeMessage/Spec.lean` / `Prysm/SyncAggregatorSelectionData/Spec.lean`')
    w(f'generalised to a field list). `{D}` (`Prysm/{X}/SpecDescription.lean`) is the independent hand `Desc` (Prysm proto).')
    if chk:
        w(f'`{chk[0]}` (`Prysm/{X}/SpecChecker.lean`, rendered by `gen/checks/desc_to_lean.py`) is the Desc checker\'s Desc of the type')
        w('(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/evidence/flat-types/`).')
    else:
        w('No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.')
    w(f'`{P}` is the SSZ content of a Go `{ty}`.')
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
    w(f'structure {P} where')
    for f in fs:
        w(f'  {f[0]} : {"UInt64" if f[1] == "u" else f"Vector UInt8 {f[2]}"}')
    w('')
    vals = ', '.join(f'.uint g.{f[0]}.toNat' if f[1] == 'u' else f'.bytes g.{f[0]}.toArray' for f in fs)
    w(f'def {P}.toValue (g : {P}) : Value :=')
    w(f'  .seq [{vals}]')
    w('')
    enc = ' ++ '.join(f'uintBytes 8 g.{f[0]}.toNat' if f[1] == 'u' else f'g.{f[0]}.toArray' for f in fs)
    w(f'def {pe} (g : {P}) : Array UInt8 :=')
    w(f'  {enc}')
    w('')
    w(f'theorem SszValue.enc_size (g : {P}) : ({pe} g).size = {N} := by')
    w(f'  simp [{pe}, Spec.uintBytes_size]')
    w('')
    lt = '; '.join(f'have := g.{f[0]}.toNat_lt' for f in us)
    w(f'theorem SszValue.toValue_fits (g : {P}) : Value.fits {D} g.toValue = true := by')
    w(f'  {lt}')
    w(f'  simp only [{D}, {P}.toValue, Value.fits, Value.fieldsFit] at *')
    w('  simp; omega')
    w('')
    n = len(fs)
    a = [f'a{i}' for i in range(n)]
    b = [f'b{i}' for i in range(n)]
    w(f'theorem SszValue.toValue_injective (g h : {P}) (e : g.toValue = h.toValue) : g = h := by')
    w(f'  obtain ⟨{", ".join(a)}⟩ := g; obtain ⟨{", ".join(b)}⟩ := h')
    w(f'  simp only [{P}.toValue, Value.seq.injEq, List.cons.injEq, Value.uint.injEq, Value.bytes.injEq,')
    w('    and_true] at e')
    inj = lambda i: (f'UInt64.toNat_inj.mp e{i}' if fs[i][1] == 'u' else f'Vector.toArray_inj.mp e{i}')
    if n == 1:
        w(f'  rw [{inj(0).replace("e0", "e")}]')
    else:
        w(f'  obtain ⟨{", ".join(f"e{i}" for i in range(n))}⟩ := e')
        w(f'  rw [{", ".join(inj(i) for i in range(n))}]')
    w('')
    w(f'theorem SszValue.toValue_surjective\' (v : Value) (h : Value.fits {D} v = true) : ∃ g : {P}, g.toValue = v := by')
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
    w(f'      by simp [{P}.toValue, {mods}]⟩')
    w('')
    pat = ', '.join(f'a{i}' if f[1] == 'u' else f'⟨r{i}, hr{i}⟩' for i, f in enumerate(fs))
    hrs = ''.join(f', hr{i}' for i, f in enumerate(fs) if f[1] == 'b')
    lt2 = '; '.join(f'have := a{i}.toNat_lt' for i, f in enumerate(fs) if f[1] == 'u')
    w(f'theorem SszValue.serialize_eq (g : {P}) : serialize {D} g.toValue = .ok ({pe} g) := by')
    w(f'  obtain ⟨{pat}⟩ := g')
    w(f'  {lt2}')
    w(f'  simp only [{D}, {P}.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk{hrs}]')
    w('  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,')
    w(f'    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Spec.uintBytes_size, bytesPerOffset, {pe},')
    w('    Desc.fieldsFixedSize, Array.append_assoc]')
    w('')
    w('/-- **Spec roundtrip.** -/')
    w(f'theorem SszValue.roundtrip (g : {P}) : deserialize {D} ({pe} g) = .ok g.toValue :=')
    w(f'  deserialize_encoding (G := {P}) (toV := {P}.toValue) (enc := {pe}) {D}_wellFormed SszValue.serialize_eq')
    w(f'    SszValue.toValue_fits g')
    w('')
    w(f'theorem SszValue.accepted_is_encoding {{bs : Array UInt8}} {{v : Value}} (h : deserialize {D} bs = .ok v) :')
    w(f'    ∃ g : {P}, v = g.toValue ∧ bs = {pe} g :=')
    w(f'  accepted_input_is_encoding (G := {P}) (toV := {P}.toValue) (enc := {pe}) {D}_wellFormed SszValue.serialize_eq')
    w(f'    SszValue.toValue_surjective\' h')
    w('')
    w(f'/-- **EthLib accepts exactly the {N}-byte inputs.** -/')
    w(f'theorem SszValue.spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize {D} bs = .ok v) ↔ bs.size = {N} := by')
    w('  constructor')
    w('  · rintro ⟨v, hd⟩')
    w(f'    obtain ⟨g, rfl, hb⟩ := SszValue.accepted_is_encoding hd')
    w(f'    rw [hb]; exact SszValue.enc_size g')
    w('  · intro h')
    rs = []
    for i, f in enumerate(fs):
        if f[1] == 'u':
            w(f'    have r{i} := readUint_lt bs {offs[i]} 8')
            rs.append(f'r{i}')
    w(f'    simp only [Nat.reducePow, Nat.reduceMul] at {" ".join(rs)}')
    gs = ', '.join(f'UInt64.ofNat (readUint bs {offs[i]} 8)' if f[1] == 'u'
                   else f'⟨bs.extract {offs[i]} {offs[i] + f[2]}, by simp; omega⟩' for i, f in enumerate(fs))
    w(f'    let g : {P} := ⟨{gs}⟩')
    w(f'    have e : bs = {pe} g := by')
    s1 = ', '.join([f'UInt64.toNat_ofNat_of_lt\' r{i}' for i, f in enumerate(fs) if f[1] == 'u']
                   + [f'uintBytes_readUint_slice bs {offs[i]} 8 (by omega)' for i, f in enumerate(fs) if f[1] == 'u'])
    w(f'      simp only [g, {pe}, {s1}]')
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
        w(f'theorem SszValue.serialize_eq_checker (g : {P}) : serialize {c} g.toValue = .ok ({pe} g) := by')
        w(f'  rw [← {D}_serialize_checker]; exact SszValue.serialize_eq g')
        w('')
        w(f'theorem SszValue.toValue_fits_checker (g : {P}) : Value.fits {c} g.toValue = true := by')
        w(f'  {lt}')
        w(f'  simp [{c}, {P}.toValue, Value.fits, Value.fieldsFit]; omega')
        w('')
        w(f'theorem SszValue.toValue_surjective_checker (v : Value) (h : Value.fits {c} v = true) :')
        w(f'    ∃ g : {P}, g.toValue = v := by')
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
        w(f'    exact deserialize_encoding (G := {P}) (toV := {P}.toValue) (enc := {pe}) checker_wellFormed')
        w(f'      SszValue.serialize_eq_checker SszValue.toValue_fits_checker g')
        w('  · intro h')
        w(f'    obtain ⟨g, rfl, hb⟩ := accepted_input_is_encoding (G := {P}) (toV := {P}.toValue) (enc := {pe})')
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
}

if __name__ == '__main__':
    out = sys.argv[1]
    for X, (ty, fs, chk) in T.items():
        os.makedirs(os.path.join(out, 'Prysm', X), exist_ok=True)
        open(os.path.join(out, 'Prysm', X, 'Spec.lean'), 'w').write(emit(X, ty, fs, chk))
        print(X)
