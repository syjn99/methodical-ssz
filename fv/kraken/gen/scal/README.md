# gen/scal — scalability stage S1–S2

Question (NEXT-PLAN after MS1, stage S): for a machine-code pattern that recurs, does a parameterized Lean
segment lemma plus an untrusted proof-text generator lower the marginal cost of the next same-pattern type,
with the same theorem statements and kernel checking? This directory holds the S2 generator and the S1/S2
evidence inputs. The method was developed on the development set only (Epoch, Slot, CommitteeIndex, Checkpoint,
AttestationData decoder; `prysm/go1.26.10/e2e/scal/HOLDOUT-MARKER.json`). Hold-out H1 (ValidatorIndex,
BeaconBlockHeader) was opened at 2026-11-10T17:53:24Z under the method freeze `56dfc27`
(`prysm/go1.26.10/e2e/scal/HOLDOUT-OPENED`). H2 (Eth1Data `UnmarshalSSZ` / `MarshalSSZTo`) was opened at
2026-11-11T01:59:11Z under the same freeze; its one `p2dec` run stopped with exit 2 (source offset 0, FINDINGS SG-1)
and the decoder was proved by hand (`E1*.lean`, `WitE1*.lean`). Result: `prysm/go1.26.10/e2e/scal/RESULT.json`.

## S1 lemmas (`lean/E2eScal/`, library `E2eScal`, own lakefile block)

| File | Content |
| --- | --- |
| `Seg.lean` | `infix_sub`: a part of an included fragment is at index k + a of the host (the code check of an instance). |
| `P1.lean` | templates `u64DecHead` / `u64DecTail` (labels, frame size, spill displacement); `u64dec_accept`: accept path of a uint64 primitive `UnmarshalSSZ`. |
| `P2Dec.lean` | templates `rootDecHead` / `rootDecMid`; `rootdec_seg`: 32-byte field decode segment (makeslice → len/cap stores → writeBarrier test → pointer store → memmove → len/cap stores → writeBarrier test). |
| `P2Enc.lean` | templates `rootEncHead` / `rootEncTail`; `rootenc_seg`: 32-byte field encode segment, fits case (length test → capacity test → spills → memmove). The growslice branch is not in the template. |
| `P1Slot.lean` | in-sample: `sl_unmarshal_accept_main_s`, statement of `E2eAd.sl_unmarshal_accept_main` word for word, proof = one application of `u64dec_accept`; `sl_same_stmt` (`rfl`: same proposition). |
| `P2DecAd.lean` | in-sample: `ad_e2e_root_s` = statement of `E2eAd.ad_e2e_root`; `rootdec_seg` + 3 instance directives (85 label, 112 reload into rbx, 113 jmp); `ad_root_same_stmt`. |
| `P2EncCpAt.lean` | `cp_enc_tmpl_at`: the encode template placement in `CpMarshal` (code-negative target; `P2EncCp` builds in about 730 s, above the 300 s case limit). |
| `Kind.lean` | frozen statement kinds `u64DecAcceptKind`, `rootDecSegKind` (`abbrev`) and `*_of`: each kind proved from its lemma (review fix-r1 M2/S1). |
| `KindAnchor.lean` | `sl_kind_anchor`, `ci_kind_anchor`: the P1 kind is the full type of the hand theorems `E2eAd.sl_unmarshal_accept_main` / `ci_unmarshal_accept_main`. |
| `P2EncCp.lean` | in-sample: `cp_e2e_marshal_main_s` = statement of `E2e.cp_e2e_marshal_main`; directives 36–62 by `rootenc_seg`, 0–35 and 63–70 the hand text verbatim; `cp_marshal_same_stmt`. |

A template is a Lean function from parameters to a directive list; the lemma takes the template's place
in the host (`IsInfixAt`) and the label address as hypotheses. An instance discharges them from the
included `.S` by computation (`infix_sub` + `simp`, `Fk.label_at'`). A wrong parameter only fails.

## S2 generator (`scalgen.py`, untrusted, Python 3 stdlib)

- `p1`: reads the `.S`, checks the 11 head and 9 tail directives textually, reads the four labels, the
  frame size, the spill (must be frame + 24) and the accept-label index; emits the P1-kind function
  theorem for the code constant, its `_kind` check and, with `--same-as`, the identity with a hand theorem.
- `p2dec`: reads the IR type (only that entry): for every 32-byte `[]byte` field its SSZ offset and Go
  offset; finds the unique decode segment whose `len` store is at Go offset + 8; checks every template
  directive and that the pointer store is at the IR Go offset and the source offset is the IR SSZ offset;
  emits one segment theorem per field (proof = the `rootdec_seg` instance) and its `_kind` check.
  Frozen generator (blob `78e3339`): a field whose code does not match (e.g. source offset 0, no `add`) stops
  the run with exit 2. That is the H2 record (historical, pre-extension). After the SG-1 extension see below.
- No mode for the encode segment yet (one development instance only).

Statement check (review fix-r1 M2, S1). Each generated theorem `t` is followed by
`t_kind : ∀ (h : Host), type_of% (@t h) = <kind> h <parameters> := by intro h; with_reducible rfl`.
The kinds are hand text in `lean/E2eScal/Kind.lean` (`u64DecAcceptKind`, `rootDecSegKind`). `*_of` there proves
each kind from its lemma; `KindAnchor.lean` shows that the P1 kind is the full type of the reviewed hand
theorems for Slot and CommitteeIndex. `@t h` is the whole declared type, binders before and after the colon,
so an added, removed or changed hypothesis in any position fails `t_kind`. No hand theorem of the instance is
needed. Not checked by `t_kind`: that the parameters of the kind are the right ones for the Go type; a wrong
parameter fails the proof (its code facts), not `t_kind`. The `exact` of the proof alone checks only the text
after the colon: a binder added before the colon still compiles (`rv-gad-extra-before`); only `t_kind` catches
it. `gen/e2e/negative.py` keeps `t_kind` in a mutant of `t`. The proofs end in `with_reducible exact`, so a
wrong conclusion literal fails at once (S2: 300 s wall timeout before, 1.4 s now).

Limit of `t_kind` (review fix-r2 N2): the `_kind` line is generator output too. Lean checks the identity, but
not WHICH kind is named: a degenerate right-hand side (e.g. `type_of% (@t h)` itself) compiles. The reader-side
check `gen/scal/kindcheck.py <file>` (no generator change) checks by text that every generated theorem `t` has
`t_kind` with right-hand side `@E2eScal.u64DecAcceptKind h C` or `@E2eScal.rootDecSegKind h C n1 … n9`
(C = the code constant of `t`'s `hk` binder), the proof `intro h; with_reducible rfl`, no local definition or
banned token, and that `lean/E2eScal/Kind.lean` has the frozen blob `3c9b95b1…` (method freeze `56dfc27`).
`--selftest`: 13 crafted cases; a degenerate copy of `GenCi.lean` fails. Not checked by it: the kind parameters
(checked only through the proof's code facts), name resolution of the kind constant, that the file builds.
A `_kind` identity is not a non-vacuity witness.

Generated (raw output, not edited): `lean/E2eScal/GenCi.lean` (CommitteeIndex accept, end to end, with
`ci_unmarshal_accept_main_g_same` against the hand theorem), `GenAdDec.lean` (AttestationData
BeaconBlockRoot segment), `GenCpDec.lean` (Checkpoint Root segment); hold-out H1 (after `HOLDOUT-OPENED`): `GenVi.lean` (ValidatorIndex
accept, `p1`, gate job 299) and `GenBhDec.lean` (three BeaconBlockHeader root segments, `p2dec`, gate job 312).
Driver: `gen/scal/gen.sh` (five `scalgen.py` commands, repo-relative; the last two are the hold-out command lines). Check: for each file, `.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh
<file> -- sh -c "<its scalgen.py command> > $REGEN_OUT"` (SAME for all three, gate job 294; SAME for GenVi / GenBhDec in review s4-r1).

Generator changes before any hold-out input are in `prysm/go1.26.10/e2e/scal/CONTAMINATION.md`:
AU-08 (commit `4581b8f`: the p2dec proof became the bare lemma instance; this checks the text after the colon
only), review fix-r1 M2/S1/S2 (the `_kind` check above, `with_reducible`). G1 — the doc comment of a p2dec
theorem was emitted before its `set_option … in` lines (Lean parse error, jobs 229/230); fixed by emitting it after.

## SG-1 extension (after both hold-outs were opened; development, not hold-out)

`scal/CONTAMINATION.md` §8. Eth1Data is development data for it. No new hold-out type is named or opened.

- Lean: `P2DecZ.lean` — template `rootDecMidZ` (`rootDecMid` without `add $src,%rbx`, 11 directives) and
  `rootdec_seg_z` (text of the hand `E1Seg0.rootdec_seg0`, names changed); `KindZ.lean` — kind
  `rootDecSegZKind` (8 parameters) and `rootDecSegZKind_of`. `Kind.lean` and `P2Dec.lean` are unchanged.
- `p2dec` form choice, generic: the directive after the buffer reload is `add $X,%rbx` (add form; X must be
  the IR SSZ offset) or `mov $0x20,%ecx` (offset-0 form; the IR SSZ offset must be 0); anything else is no match.
  The header imports `E2eScal.KindZ` only when an offset-0 segment is emitted.
- Field rule: each field is matched on its own. Exit 0 = every field, whole file on stdout. Exit 3 = some
  fields match: nothing on stdout, one line per field on stderr; `--partial-out FILE` writes the matched
  fields under a `PARTIAL OUTPUT` header naming the missing ones. Exit 2 = no field matches, two fields claim
  overlapping directives, or the IR read fails: nothing is written.
- Output: `lean/E2eScal/GenE1Dec.lean` (raw, `gen.sh` last line), DepositRoot (offset-0) and BlockHash
  (add form). `E1GenSame.lean` shows `rootDecMidZ = E1.rootDecMid0`, the same lemma statement (`rfl`), and
  that the generated DepositRoot theorem gives the conclusion of the hand `rootdec_seg0`.
- `kindcheck.py` accepts `@E2eScal.rootDecSegZKind h C n1 … n8` only with `KindZ.lean` at its pinned blob.
- Tests: `p2dec_test.py` (old generator from its git blob still exits 2 with the recorded stderr; new
  generator output = committed; 7 crafted `.S` mutants exit 2/3 with 0 bytes on stdout; partial file marked)
  → `scal/sg1-gen-test.json`; negatives `negcases-sg1.json` → `scal/negative-sg1.json`.
- Not covered: the inline DepositCount read, encode mode, loops, other compilers or flags.

## Evidence files

- `AxiomsScal.lean`: `#print axioms` of every S1/S2 theorem (checked with `gen/e2e/axioms.py`).
- `negcases-scal.json`: code / statement mutants and controls for the in-sample and generated theorems
  (run with `gen/e2e/negative.py`).
- `tcost.py` → `prysm/go1.26.10/e2e/scal/TEMPLATE-COST.json` (template cost, separate from hold-out cost).

## Results

Kernel-checked: all 13 modules of `E2eScal` (count by command: `ls fv/kraken/lean/E2eScal/*.lean | wc -l` = 13; 11 before `Kind`, `KindAnchor`; audit AU-13). Axioms: 22 names (`grep -c '^#print axioms' gen/scal/AxiomsScal.lean`), standard only (`scal/axioms.json`, job 292; 15 names at job 247).
Negatives: 18/18 (6 controls pass, 12 mutants fail inside their theorem; `scal/negative-result.json`, jobs 242, 246).
Audit AU-08: 20/20 after the two `*-stmt-extra` cases were added (jobs 258, 259).
Review fix-r1: 28/28 (6 controls, 22 inside) after 8 new statement cases; GenCi / GenAdDec / GenCpDec cases rerun after regeneration, one gated job per batch (jobs 288–291).
Cost: `scal/TEMPLATE-COST.json` (jobs 214–247; 31 gate jobs, 24 lake runs, 13 failed, 2271 cumulative gate s — 2203 s of them the
P2 encode in-sample — peak 1.83 GiB, no memcap kill).
`P2EncCp` alone: about 730 s in its own build (job record in `TEMPLATE-COST.json`), 986.0 s in the review fix-r1 run of the unchanged file (n = 1; `opt1/AU-07.json`).
