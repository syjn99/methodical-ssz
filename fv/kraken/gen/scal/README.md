# gen/scal — scalability stage S1–S2 (run fve2e-20261110T010000Z-2dd40dab, INBOX 011)

Question (NEXT-PLAN after MS1, stage S): for a machine-code pattern that recurs, does a parameterized Lean
segment lemma plus an untrusted proof-text generator lower the marginal cost of the next same-pattern type,
with the same theorem statements and kernel checking? This directory holds the S2 generator and the S1/S2
evidence inputs. Development set only (Epoch, Slot, CommitteeIndex, Checkpoint, AttestationData decoder);
the hold-out types were not opened (`prysm/go1.26.10/e2e/scal/HOLDOUT-MARKER.json`).

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
| `P2EncCp.lean` | in-sample: `cp_e2e_marshal_main_s` = statement of `E2e.cp_e2e_marshal_main`; directives 36–62 by `rootenc_seg`, 0–35 and 63–70 the hand text verbatim; `cp_marshal_same_stmt`. |

A template is a Lean function from parameters to a directive list; the lemma takes the template's place
in the host (`IsInfixAt`) and the label address as hypotheses. An instance discharges them from the
included `.S` by computation (`infix_sub` + `simp`, `Fk.label_at'`). A wrong parameter only fails.

## S2 generator (`scalgen.py`, untrusted, Python 3 stdlib)

- `p1`: reads the `.S`, checks the 11 head and 9 tail directives textually, reads the four labels, the
  frame size, the spill (must be frame + 24) and the accept-label index; emits the P1-kind function
  theorem for the code constant and, with `--same-as`, the statement-identity check.
- `p2dec`: reads the IR type (only that entry): for every 32-byte `[]byte` field its SSZ offset and Go
  offset; finds the unique decode segment whose `len` store is at Go offset + 8; checks every template
  directive and that the pointer store is at the IR Go offset and the source offset is the IR SSZ offset;
  emits one segment theorem per field (statement = `rootdec_seg` with the code hypotheses of the
  function). A field whose code does not match (e.g. source offset 0, no `add`) stops with exit 2.
- No mode for the encode segment yet (one development instance only).

Generated (raw output, not edited): `lean/E2eScal/GenCi.lean` (CommitteeIndex accept, end to end, with
`ci_unmarshal_accept_main_g_same` against the hand theorem), `GenAdDec.lean` (AttestationData
BeaconBlockRoot segment), `GenCpDec.lean` (Checkpoint Root segment). Driver: the stream's
`scratch/s6/gen1.sh` (three `scalgen.py` commands: `p1` on the CommitteeIndex `.S` with `--const CiUnmarshal
--same-as E2eAd.ci_unmarshal_accept_main`; `p2dec` on the AttestationData and Checkpoint decoders with `--type
v1alpha1.AttestationData` / `v1alpha1.Checkpoint`), gate jobs 227 and 236.

Generator fixes during development (before any hold-out input): G1 — the doc comment of a p2dec theorem
was emitted before its `set_option … in` lines (Lean parse error, jobs 229/230); fixed by emitting it after.

## Evidence files

- `AxiomsScal.lean`: `#print axioms` of every S1/S2 theorem (checked with `gen/e2e/axioms.py`).
- `negcases-scal.json`: code / statement mutants and controls for the in-sample and generated theorems
  (run with `gen/e2e/negative.py`).
- `tcost.py` → `prysm/go1.26.10/e2e/scal/TEMPLATE-COST.json` (template cost, separate from hold-out cost).

## Results (session 6)

Kernel-checked: all 14 modules of `E2eScal`. Axioms: 15 names, standard only (`scal/axioms.json`, job 247).
Negatives: 18/18 (6 controls pass, 12 mutants fail inside their theorem; `scal/negative-result.json`, jobs 242, 246).
Cost: `scal/TEMPLATE-COST.json` (31 gate jobs, 24 lake runs, 13 failed, 2271 gate s — 2203 s of them the
P2 encode in-sample — peak 1.83 GiB, no memcap kill).
