"""Evidence tool (not part of gen/scal): write lean/E2eScal/F24<X>Spec.lean, the spec bridge of each type
(the text of SmSpec.lean / SaSpec.lean generalised to a field list: P structure, encoding, serialize, roundtrip,
accepts-iff-size, spec reject; codec equality with the checker Desc where a Desc-checker record exists).
usage: python3 -I -B f24spec.py <fv/kraken/lean/E2eScal>"""
import sys, os

T = {  # X: (Go type, fields [(name, 'u'|'b', n)], checker (lean name, names) or None)
 'Dpr': ('v1.DepositRequest', [('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                               ('signature', 'b', 96), ('index', 'u', 8)],
         ('dprCheckerDesc', None)),
 'Bdr': ('v1.BuilderDepositRequest', [('pubkey', 'b', 48), ('withdrawalCredentials', 'b', 32), ('amount', 'u', 8),
                                      ('signature', 'b', 96)], None),
 'Bbr': ('v1alpha1.BeaconBlocksByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8), ('step', 'u', 8)], None),
 'Bsr': ('v1alpha1.BlobSidecarsByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'Epr': ('v1alpha1.ExecutionPayloadEnvelopesByRangeRequest', [('startSlot', 'u', 8), ('count', 'u', 8)], None),
 'Pdc': ('v1alpha1.PartialDataColumnGroupID', [('beaconBlockRoot', 'b', 32), ('slot', 'u', 8)], None),
 'Vid': ('v1alpha1.ValidatorIdentity', [('index', 'u', 8), ('pubkey', 'b', 48), ('activationEpoch', 'u', 8)], None),
 'Bpf': ('v1alpha1.BuilderPreferences', [('maxExecutionPayment', 'u', 8)], None),
}


def kind(f):
    return '.uint 8' if f[1] == 'u' else f'.byteVector {f[2]}'


def emit(X, ty, fs, chk):
    x = X.lower()
    P, pe, pp = f'P{X}', f'p{x}Enc', f'p{x}'
    D = f'prysm{X}Desc'
    N = sum(f[2] for f in fs)
    us = [f for f in fs if f[1] == 'u']
    offs, o = [], 0
    for f in fs:
        offs.append(o)
        o += f[2]
    L = []
    w = L.append
    w('import E2e.Spec')
    w('import E2e.SpecEq')
    w('import E2eScal.F24Desc')
    if chk:
        w(f'import E2eScal.F24{X}SpecChecker')
    w('')
    w('/-!')
    w(f'# Spec bridge for the real Prysm `{ty}` (FLAT24 / H7)')
    w('')
    w('Written by the FLAT24 evaluator with its evidence script `f24spec.py` (the text of `SmSpec.lean` / `SaSpec.lean`')
    w(f'generalised to a field list). `{D}` (`F24Desc.lean`) is the independent hand `Desc` (Prysm proto).')
    if chk:
        w(f'`{chk[0]}` (`F24{X}SpecChecker.lean`, rendered by `gen/e2e/descterm.py`) is the Desc checker\'s Desc of the type')
        w('(the producer output recorded in `gen/desc/results/main.result.json`, same sha256; copy in `prysm/go1.26.10/e2e/f24/`).')
    else:
        w('No Desc-checker record exists for this type (`gen/desc/results/main.result.json`): no codec equality here.')
    w(f'`{P}` is the SSZ content of a Go `{ty}`.')
    w('-/')
    w('')
    w('namespace E2e')
    w('open EthLib.Serialization.Ssz Fv1')
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
    w(f'theorem {pp}_enc_size (g : {P}) : ({pe} g).size = {N} := by')
    w(f'  simp [{pe}, Fv.uintBytes_size]')
    w('')
    lt = '; '.join(f'have := g.{f[0]}.toNat_lt' for f in us)
    w(f'theorem {pp}_toValue_fits (g : {P}) : Value.fits {D} g.toValue = true := by')
    w(f'  {lt}')
    w(f'  simp only [{D}, {P}.toValue, Value.fits, Value.fieldsFit] at *')
    w('  simp; omega')
    w('')
    n = len(fs)
    a = [f'a{i}' for i in range(n)]
    b = [f'b{i}' for i in range(n)]
    w(f'theorem {pp}_toValue_injective (g h : {P}) (e : g.toValue = h.toValue) : g = h := by')
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
    w(f'theorem {pp}_toValue_surjective\' (v : Value) (h : Value.fits {D} v = true) : ∃ g : {P}, g.toValue = v := by')
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
    w(f'theorem {pp}_serialize (g : {P}) : serialize {D} g.toValue = .ok ({pe} g) := by')
    w(f'  obtain ⟨{pat}⟩ := g')
    w(f'  {lt2}')
    w(f'  simp only [{D}, {P}.toValue, serialize, serializeStruct, serializeFields, Vector.toArray_mk{hrs}]')
    w('  simp (config := {decide := true}) [*, bind, Except.bind, pure, Except.pure, assemble, headWidth, bodyWidth,')
    w(f'    headOf, bodiesOf, Desc.isFixed, Desc.fixedSize, Fv.uintBytes_size, bytesPerOffset, {pe},')
    w('    Desc.fieldsFixedSize, Array.append_assoc]')
    w('')
    w('/-- **Spec roundtrip.** -/')
    w(f'theorem {pp}_roundtrip (g : {P}) : deserialize {D} ({pe} g) = .ok g.toValue :=')
    w(f'  deserialize_enc (G := {P}) (toV := {P}.toValue) (enc := {pe}) {D}_wellFormed {pp}_serialize')
    w(f'    {pp}_toValue_fits g')
    w('')
    w(f'theorem {pp}_accepted_is_enc {{bs : Array UInt8}} {{v : Value}} (h : deserialize {D} bs = .ok v) :')
    w(f'    ∃ g : {P}, v = g.toValue ∧ bs = {pe} g :=')
    w(f'  accepted_is_enc (G := {P}) (toV := {P}.toValue) (enc := {pe}) {D}_wellFormed {pp}_serialize')
    w(f'    {pp}_toValue_surjective\' h')
    w('')
    w(f'/-- **EthLib accepts exactly the {N}-byte inputs.** -/')
    w(f'theorem {pp}_spec_accepts_iff (bs : Array UInt8) : (∃ v, deserialize {D} bs = .ok v) ↔ bs.size = {N} := by')
    w('  constructor')
    w('  · rintro ⟨v, hd⟩')
    w(f'    obtain ⟨g, rfl, hb⟩ := {pp}_accepted_is_enc hd')
    w(f'    rw [hb]; exact {pp}_enc_size g')
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
    w(f'    exact ⟨_, {pp}_roundtrip g⟩')
    w('')
    w(f'/-- `len(buf) ≠ {N}`: EthLib rejects. -/')
    w(f'theorem {pp}_spec_rejects (bs : Array UInt8) (h : bs.size ≠ {N}) : ∃ e, deserialize {D} bs = .error e := by')
    w(f'  cases hd : deserialize {D} bs with')
    w('  | error e => exact ⟨e, rfl⟩')
    w(f'  | ok v => exact absurd (({pp}_spec_accepts_iff bs).mp ⟨v, hd⟩) h')
    w('')
    if chk:
        c = chk[0]
        w('/-! ### The checker Desc decodes like the hand Desc (accepted inputs and values) -/')
        w('')
        w(f'theorem {X.lower()}Checker_wellFormed : {c}.wellFormed = .ok () := by rfl')
        w('')
        w(f'theorem {pp}_serialize_checker (g : {P}) : serialize {c} g.toValue = .ok ({pe} g) := by')
        w(f'  rw [← {D}_serialize_checker]; exact {pp}_serialize g')
        w('')
        w(f'theorem {pp}_toValue_fits_checker (g : {P}) : Value.fits {c} g.toValue = true := by')
        w(f'  {lt}')
        w(f'  simp [{c}, {P}.toValue, Value.fits, Value.fieldsFit]; omega')
        w('')
        w(f'theorem {pp}_toValue_surjective_checker (v : Value) (h : Value.fits {c} v = true) :')
        w(f'    ∃ g : {P}, g.toValue = v := by')
        w(f'  have h\' : Value.fits {D} v = true := by')
        w(f'    cases v <;> simp_all [{D}, {c}, Value.fits]')
        w(f'  exact {pp}_toValue_surjective\' v h\'')
        w('')
        w('/-- **Codec equality on the accepted inputs**. -/')
        w(f'theorem {D}_deserialize_checker (bs : Array UInt8) (v : Value) :')
        w(f'    deserialize {D} bs = .ok v ↔ deserialize {c} bs = .ok v := by')
        w('  constructor')
        w('  · intro h')
        w(f'    obtain ⟨g, rfl, hb⟩ := {pp}_accepted_is_enc h')
        w('    rw [hb]')
        w(f'    exact deserialize_enc (G := {P}) (toV := {P}.toValue) (enc := {pe}) {X.lower()}Checker_wellFormed')
        w(f'      {pp}_serialize_checker {pp}_toValue_fits_checker g')
        w('  · intro h')
        w(f'    obtain ⟨g, rfl, hb⟩ := accepted_is_enc (G := {P}) (toV := {P}.toValue) (enc := {pe})')
        w(f'      {X.lower()}Checker_wellFormed {pp}_serialize_checker {pp}_toValue_surjective_checker h')
        w(f'    rw [hb]; exact {pp}_roundtrip g')
        w('')
    w('end E2e')
    return '\n'.join(L) + '\n'


descnames = {
 'Dpr': ['pubkey', 'withdrawal_credentials', 'amount', 'signature', 'index'],
 'Bdr': ['pubkey', 'withdrawal_credentials', 'amount', 'signature'],
 'Bbr': ['start_slot', 'count', 'step'], 'Bsr': ['start_slot', 'count'], 'Epr': ['start_slot', 'count'],
 'Pdc': ['beacon_block_root', 'slot'], 'Vid': ['index', 'pubkey', 'activation_epoch'],
 'Bpf': ['max_execution_payment'],
}

if __name__ == '__main__':
    out = sys.argv[1]
    for X, (ty, fs, chk) in T.items():
        open(os.path.join(out, f'F24{X}Spec.lean'), 'w').write(emit(X, ty, fs, chk))
        print(X)
