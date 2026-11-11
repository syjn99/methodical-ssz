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
| `P2EncCpAt.lean` | `cp_enc_tmpl_at`: the encode template placement in `CpMarshal` (code-negative target; before the AU-07 fix `P2EncCp` built in about 730 s, above the 300 s case limit; after it see `opt1/AU-07.json` attempt 4). |
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
Driver: `gen/scal/gen.sh` (six `scalgen.py` commands, repo-relative; the fourth and fifth are the hold-out H1 command lines, the last is the SG-1 extension output `GenE1Dec.lean`). Check: for each file, `.claude/skills/maintaining-methodical-fv/scripts/regen_check.sh
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
- `negcases-t9.json`: mutants and controls for the BeaconBlockHeader encoder fast path (T-9 hand proof;
  `scal/negative-t9.json`, one gated job per case). Not generator output.
- `tcost.py` → `prysm/go1.26.10/e2e/scal/TEMPLATE-COST.json` (template cost, separate from hold-out cost).

## Results

Kernel-checked: all 13 modules of `E2eScal` (count by command: `ls fv/kraken/lean/E2eScal/*.lean | wc -l` = 13; 11 before `Kind`, `KindAnchor`; audit AU-13). Axioms: 22 names (`grep -c '^#print axioms' gen/scal/AxiomsScal.lean`), standard only (`scal/axioms.json`, job 292; 15 names at job 247).
Negatives: 18/18 (6 controls pass, 12 mutants fail inside their theorem; `scal/negative-result.json`, jobs 242, 246).
Audit AU-08: 20/20 after the two `*-stmt-extra` cases were added (jobs 258, 259).
Review fix-r1: 28/28 (6 controls, 22 inside) after 8 new statement cases; GenCi / GenAdDec / GenCpDec cases rerun after regeneration, one gated job per batch (jobs 288–291).
Cost: `scal/TEMPLATE-COST.json` (jobs 214–247; 31 gate jobs, 24 lake runs, 13 failed, 2271 cumulative gate s — 2203 s of them the
P2 encode in-sample — peak 1.83 GiB, no memcap kill).
`P2EncCp` alone: about 730 s in its own build (job record in `TEMPLATE-COST.json`), 986.0 s in the review fix-r1 run of the unchanged file (n = 1; `opt1/AU-07.json`).

## GEN2 (unit G2-G; development set, after H3; review g2g-r1 REQUEST_CHANGES, documents only, closed by G2-F)

`scal/CONTAMINATION.md` §14. Lemmas: unit G2-L (`SegN`, `KindN`, `U64Inline`, `KindU64`, `Compose`).

- Compatibility switch: the new coverage is only behind `--gen2`. Without it `p2dec` writes the S2 / SG-1 text
  byte for byte (`regen_check.sh` SAME for the 8 earlier commands: `gen.sh` 6, H3 2).
- `p2dec --gen2 [--summary FILE.json] [--partial-out FILE]`: every IR field is classified. Byte vectors of 32
  bytes keep the old theorem text (`rootdec_seg` / `rootdec_seg_z`); 48 / 96 bytes use `bytesdec_seg` /
  `bytesdec_seg_z` (kinds `bytesDecSegKind` / `bytesDecSegZKind`); `uint64` fields use `u64dec_inline_seg`
  (kind `u64DecInlineSegKind`). Anything else is "not covered: <reason>" on stderr and in the summary JSON.
  Exit codes as for `p2dec` (0 / 3 / 2); the covered segments must be in IR field order in the code.
- `p2dec --gen2 --compose --name T [--same-as HAND]`: the whole accept theorem from `dechead_seg`, the generated
  segments (module of the same `--prefix` in `--imports`), `bytesdec_tail_seg` and `decepi_seg`. Its only
  statement check is `T_type`, the identity with the hand theorem `HAND`. Without `--same-as` the statement
  is unchecked; the run says so and `kindcheck.py` fails the file. There is no kind for a composed statement.
- Output (raw, unedited; `gen.sh` last six commands): `Gen2E1Dec`, `Gen2BiDec`, `Gen2DmDec` (3/3, 2/2, 3/3
  fields), `Gen2BiAccept`, `Gen2DmAccept`, `Gen2E1Accept` (identity with `Bi.bi_e2e_accept_main`,
  `Dm.dm_e2e_accept_main`, `E1.e1_e2e_accept_main`). Hand compositions over the generated segments:
  `BiAcceptG2.lean`, `DmAcceptG2.lean`.
- `kindcheck.py` accepts the three new kinds only with `KindN` / `SegN` and `KindU64` / `U64Inline` at their
  pinned blobs, and reports a `_type` identity as "identity-checked" (not a kind). Selftest: 52 cases.
- Tests: `p2dec_test.py` (43 cases), negatives `negcases-g2g.json` (17 cases).
- Not covered: delegated overlay fields (compiled as a call), other vector sizes, displacement 0 for
  uint64, nested containers, lists, bitfields, encoders; compose needs frame `0x20` and the receiver in rdx.

## GEN2 fixes (unit G2-F; after review g2g-r1, before the H4 freeze; review g2f-r1 APPROVE on `eacf0fb`; g2f-r1 S1–S4 checker changes are open proposals, not done)

`scal/CONTAMINATION.md` §15. Default mode and every committed output unchanged (`regen_check.sh` 15/15 SAME).

- `kindcheck.py` (review S1): a `_type` identity is accepted ONLY for a composed accept theorem (its proof uses
  `E2eScal.dechead_seg` and `E2eScal.decepi_seg`), never in place of a segment `_kind`. Its right-hand side must
  not be under `E2eScal.Gen…` and must not be declared in a `lean/E2eScal/Gen*.lean` module. A theorem line with
  `UNCHECKED STATEMENT` fails. The PASS line reads "identity against X — statement evidence only if X is an
  independent hand statement": whether X is independent is for a human to confirm. Selftest: 70 cases; seven
  deliberately broken checker copies (one per new rule) each fail it.
- `p2dec --gen2 --partial-out FILE` (exit 3, stdout empty): FILE is a valid Lean module. Imports first, then the
  `PARTIAL OUTPUT` header with one line `UNCOVERED-JSON: [{"field": …, "reason": …}, …]`, then the covered
  fields' segment theorems and kinds. Example: `lean/E2eScal/Gen2BhDecPartial.lean` (BeaconBlockHeader 3/5).
  The default mode (no `--gen2`) keeps its old partial text.
- `kindcheck.py FILE` still rejects a partial file. `kindcheck.py --partial FILE` checks the kinds of the present
  theorems: exit 3 with the line `PARTIAL n/m fields: kinds of present theorems checked; NOT a full-coverage
  result`, 1 on failure, 2 usage; never 0.
- `--compose` refuses (exit 2, nothing written, no partial file) when a field is not covered or the code is
  outside the shape: frame `0x20`, spills `0x30` / `0x38`, first field a byte vector at directive 13, receiver
  in rdx, fields contiguous in IR order, epilogue after the last field. `--imports` must supply any per-type
  module the proof calls (e.g. `E2eScal.E1Accept` for `e1_lo`).
- `--same-as NAME`: NAME must be an independently written hand statement (a hand theorem; not generated).
  `--same-as-prop NAME`: NAME is a hand-written Prop-valued `abbrev NAME [Host] : Prop`; emits
  `T_type : ∀ (h : Host), type_of% (@T h) = @NAME h` (tested with a scratch fixture, not in the library).
  Without either, the theorem line carries `-- UNCHECKED STATEMENT: checked by nobody` (exit 0; kindcheck fails).
- Tests: `p2dec_test.py` 51 cases (G2-F: partial module, BeaconBlockHeader partial, four compose refusals,
  the marker, a generated `--same-as`, `--same-as-prop`).

## H4 hold-out with the frozen GEN2 generator (method freeze `eacf0fb`; review h4-r1 APPROVE on `fae7d6f`)

- One `--gen2` run and one `--compose` run per type; raw output unedited (`h4/gen/`, `lean/E2eScal/Gen2DdDecPartial.lean`).
- Deposit_Data: exit 3, 3 of 4 fields (PublicKey and Amount near-in-sample, Signature out-of-sample). WithdrawalCredentials
  not covered: a padding `nop` before `callq runtime.makeslice` (FINDINGS SG-3).
- PendingPartialWithdrawal: exit 2, 0 of 3 (two overlay-typed fields compiled as calls; an inline uint64 read with the
  receiver in rax, interleaved). `--compose` refused both types: no generated whole proof exists for a hold-out type.
- The development-set coverage above is in-sample; it did not transfer unchanged. Proposals P-H4-1..3 are not done.

## GEN3 (unit G3-G; generator change after H4, development set only; reviewed g3g-r1 APPROVE on `6dc0e2a`, the H5 method freeze)

`scal/CONTAMINATION.md` §19. Lemmas: unit G3-L (`CallDec`, `KindCall`, `U64RR`, `SegNPad`, `KindAccept`).
In-sample coverage only; no hold-out claim until H5.

- Compatibility switch: the new shapes are only behind `--gen3` (it implies `--gen2`). Default and `--gen2`
  output unchanged: `regen_check.sh` SAME for the 16 earlier commands; base-vs-head differential (default,
  `--gen2`, `--gen2 --compose`, 10 inputs) 30/30 equal.
- `p2dec --gen3 [--summary FILE.json] [--partial-out FILE]` adds three shapes:
  - a `uint64`-overlay field decoded by a call to `primitives.{Slot,CommitteeIndex,ValidatorIndex,Epoch}.UnmarshalSSZ`
    (callees with a proved accept spec): call block `calldec_seg` (`<p>_<field>_call`, hypothesis
    `hC : U64CalleeAcc "<callee>"`) plus the argument set-up, one of `callarg_first_seg pad` (SSZ offset 0),
    `callarg_reload_seg pad`, or the `lea` form `callarg_lea_seg` + [two-directive read of the IR field just
    before] + `callarg_mov_seg` (`_arg`, or `_arg1` / `_arg2`);
  - the two-directive uint64 read `mov src(%rbx),%rX; mov %rX,f(%rax)` (`u64dec_rr_seg`, register in the kind);
  - a byte vector with one padding `nop` between `mov $n,%ecx` and `callq runtime.makeslice`, add form
    (`bytesdec_seg_p true n`, kind `bytesDecSegKind`).
  Anything else is "not covered: <reason>". Exit codes as for `--gen2`.
- `--gen3 --compose`: refuses types with callee or two-directive fields (exit 2). Otherwise the GEN2
  composition plus `T_kind : type_of% (@T h) = @E2eScal.decAcceptKind h C st [fields] jret` (`rfl` at default
  transparency under `set_option maxHeartbeats 200000 in`; a timeout is a build failure). `--same-as-prop`
  adds the identity with a hand statement.
- Output (raw, unedited; `gen.sh` last five commands): `Gen3PwDec` 3/3, `Gen3DdDec` 4/4, `Gen3BhDec` 5/5,
  `Gen3AdDecPartial` 3/5 (exit 3), `Gen3DdAccept2` (composed). Run 1 of the compose command wrote a doc
  comment before `set_option … in` and did not parse; that file is kept unedited as
  `scal/gen3/Gen3DdAccept.run1-parse-error.lean.txt`. Hand compositions over the generated theorems:
  `PwAcceptG3.lean`, `BhAcceptG3.lean`.
- `kindcheck.py`: the six GEN3 kinds with `KindCall` / `CallDec` / `U64RR` pinned, callee list,
  `SegNPad` pin for `bytesdec_seg_p`, `decAcceptKind` on composed theorems only (`KindAccept` pinned);
  review g2f-r1 S1–S4 (rule 6a on comment-stripped text; coverage `n of m` with n ≠ m fails in the default
  mode; n must equal the fields with theorems; exit-code controls). Selftest 114 cases + 4 exit-code cases.
- Tests: `p2dec_test.py` (GEN3 cases `g3-*`), negatives `negcases-g3g.json`.
- Not covered: other set-up forms (other registers, extra moves), callees without a proved spec, pointer /
  nested-container fields, lists, bitfields, sizes other than 32 / 48 / 96, a `nop` elsewhere (also the
  observed tail `nop` of BeaconBlockHeader.ParentRoot / Checkpoint.Root, which `--compose` does not read),
  the offset-0 form with a `nop`, encoders; composed theorems with callee fields or frames other than `0x20`.
- Review g3g-r1 (APPROVE, 0 must-fix; records added at integration INT5):
  - "n/m covered" means the template directives of n fields are proved; it is not a decoder proof. The
    first-field set-up form carries no SSZ offset parameter, and directives outside the template spans are not
    read (S1). Take n/m from the exit code and `--summary`.
  - Also not covered (S3): a plain `uint64` at SSZ offset 0 or Go offset 0 (`u64_find_gen3` refuses); the `lea`
    set-up form needs the two-directive read of the IR field just before.
  - The base-vs-head differential is byte-equal for every output; only the argparse usage text changed (it lists
    `[--gen3]`) (S6). Checkpoint, reviewer run: 2/2 fields, `--compose` refuses (S5; no committed file).
  - OPEN, not done (S2, checker change): require the coverage header for `--gen2` / `--gen3` files; strip string
    literals in rule 6a. Until then `kindcheck.py` output is evidence only for a file byte-equal to a
    regeneration (`regen_check.sh`).
- Hold-out H5 (frozen at `6dc0e2a`; h5-r1 APPROVE): SyncCommitteeMessage 2/4, PendingConsolidation 1/2, both
  near-in-sample by field kind; `--compose` refused both. Missed forms (proposals P-H5-1..3, not done): receiver
  reloaded into rax in the 32-byte segment, call set-up with the receiver already in rax, padding `nop` after a call.
`P2EncCp` alone, before the AU-07 fix: about 730 s in its own build (job record in `TEMPLATE-COST.json`), 986.0 s in the review fix-r1 run of the unchanged file (n = 1; `opt1/AU-07.json`).
After the AU-07 fix: see `opt1/AU-07.json` attempt 4.

## GEN4 (unit G4-G; generator change after H5, development set only; g4g-r1 REQUEST_CHANGES, fixed below)

`scal/CONTAMINATION.md` §22. Lemmas: unit G4-L (`NopView`, `StepK`, `KindStep`, `CallReg`, `SegReg`, `SegRegZ`,
`KindSegReg`; review g4l-r1 APPROVE). In-sample coverage only; no hold-out claim until H6.

- Compatibility switch: `--gen4` is its own code path. Default, `--gen2`, `--gen3` output unchanged:
  `regen_check.sh` SAME for the 23 earlier commands.
- `p2dec --gen4 [--summary FILE.json] [--partial-out FILE]`: no multi-directive set-up templates. The generator walks
  the accept path from the end of the decoder head (prologue, spills, `test %al,(%rax)`) with a small dataflow over
  registers and stack slots (receiver `rcv + o`, buffer `bf + o`, immediates, buffer bytes, slice pointer, unknown):
  - step forms `mov %rS,%rD`, `mov d(%rB),%rD` (value form `kstep_ldv` for receiver / buffer / pointer / immediate
    words, else bytes form `kstep_ldb`), `mov %rS,d(%rB)`, `lea d(%rB),%rD`, `add $i,%rD`, `mov $i,%eD`, `jmp l`,
    `l:` → one theorem `<prefix>_s<index>` with its `_kind` (`KindStep`);
  - `nop` → nothing; it is a leading nop of the next window (L1 window rule);
  - `callq <Slot|CommitteeIndex|ValidatorIndex|Epoch>.UnmarshalSSZ` → the call window `nop* callq nop* test nop* je`
    (`calldec_seg_w`, kind `callDecSegKindG4`) ONLY when rax = rcv + (IR Go offset), rbx = bf + (IR SSZ offset),
    rcx = 8 and the field is the next IR field;
  - `lea type__+387072(%rip),%rax` → the byte segment over two windows (`bytesdec_seg_g4` / `_z_g4`) ONLY when the
    reload slots hold receiver / buffer, rX ∈ {rdx, rsi}, rY ∈ {rax, rcx, rdx, rsi, rdi}, n ∈ {32, 48, 96},
    fP / src = IR, fL = fP + 8, fC = fP + 16;
  - anything else stops the walk: the remaining fields are "not covered: <reason>" with a miss class
    (padding / register / set-up order / new directive form / new field kind / other) in `--summary`.
  "ONLY when" above is the walker's acceptance rule, not a checked fact: see "What covered means" below.
  A field is complete at its own event (call block; store of the buffer bytes at the IR SSZ offset into the IR Go offset;
  store of the slice pointer after the segment). Events out of IR order stop the walk. The output lists its fields
  in a `FIELDS-JSON:` line. Exit codes 0 / 3 / 2 as for `--gen2`.
- `--gen4 --compose` refuses (exit 2): no kind for field compositions, composed GEN4 statements or the head / epilogue
  lemmas. `--gen3 --compose` without `--same-as*` now writes `UNCHECKED STATEMENT` (review g3g-r1); `kindcheck.py`
  rejects it, and also rejects a composed theorem with `decAcceptKind` but no hand identity (rule 6d).
- Output (raw, unedited; `gen.sh` last block): `Gen4CpDec` 2/2, `Gen4AdDecPartial` 3/5, `Gen4BhDec` 5/5, `Gen4E1Dec`
  3/3, `Gen4BiDec` 2/2, `Gen4DmDec` 3/3, `Gen4DdDec` 4/4, `Gen4PwDec` 3/3, `Gen4SmDec` 4/4, `Gen4PcDec` 2/2. Hand
  compositions over them: `SmAcceptG4gen.lean`, `PcAcceptG4gen.lean`, `PwAcceptG4gen.lean` (types = `H5.sm_accept_stmt`,
  `H5.pc_accept_stmt`, `H4.pw_accept_stmt`).
- `kindcheck.py` rule 10: the GEN4 kinds with the G4-L modules pinned, the proof's lemma = the kind's lemma (comments
  and strings removed), `FIELDS-JSON` coverage; rule 11 (review g3g-r1 S2): coverage header required for GEN2+ kinds,
  string literals stripped in rule 6a. Label strings in `stepLabelKind` / `stepJmpKind` / `callDecSegKindG4` are
  phantom parameters (review g4l-r1): not checked by the kind line. Selftest 157 + 4 cases; 14 broken copies fail it.
- Tests: `p2dec_test.py` GEN4 cases `g4-*` (10 types, compose refusal, 35 dataflow mutants); negatives
  `negcases-g4g.json` (17).
- Not covered: nested containers / pointer callees, callees without a proved spec, lists, bitfields, sizes other than
  32 / 48 / 96, receiver registers outside the lemma sets, index / rip / immediate-store operands, head and epilogue
  emission, encoders.

### Unit G4-F (fixes after review g4g-r1; g4f-r1 REQUEST_CHANGES, fixed in G4-F2)

**What "covered" means.** A field marked "covered" by `--gen4` is the GENERATOR's claim: its walker believes that
the code before each emitted block establishes the block's entry state. Each emitted theorem is kernel-checked on its
own (its code fact `he` by `rfl`, its `_kind` line). Its entry facts (register values, the memory fact `hm`, the call
block's `dst` / `src`) are hypotheses. Nothing kernel-checks that the chain of steps establishes a block's entry
state, or that a call block belongs to the IR field named in `FIELDS-JSON`. Only a field composition does that, and
field compositions are hand text (three development types have one: SyncCommitteeMessage, PendingConsolidation,
PendingPartialWithdrawal). So a result (S) of a hold-out counts "walker-covered + each theorem builds", not
"field proved". Review g4g-r1 found seven inputs on which the walker of `21b8aab` said "covered" although the code
did not establish the entry state (every theorem still built); the rules below refuse them.

- Head (M1b): directives 0–10 must be the `decpro_seg` prologue (`HeadN.lean`, `decPro`): two labels; directives
  2–8 `cmp 0x10(%r14),%rsp; jbe; push %rbp; mov %rsp,%rbp; sub $F,%rsp; mov %rbx,dB(%rsp)` in this order plus one
  `nop`; `cmp $size,%rcx` at 9 and `jne` at 10. The head is positional. Spills of rax / rbx / rcx / rdi are read only
  after directive 10 (after the frame is set up). A head miss exits 2, and `--summary` lists every field with
  `reached: false`, the reason and the class (`padding` when the head matches with its nops erased, else `other`).
- Stack-store rule (M1a): an 8-byte store `mov %r,d(%rsp)` (also a head spill and the segment's pointer slot) is
  modelled only when `d` is a multiple of 8 and lies in `[0, F)` (frame) or `[F + 16, F + 48)` (the argument spill
  area). Otherwise the walk stops (class `other`). A store invalidates every tracked slot it overlaps. After a call
  block only `sp + 8` changes (the callee's spill, stated by `calldec_seg_w`); after a segment `[sp, sp + 24)` changes.
- A write to rbp or r14 (part of every block's entry: `rbp0`, the stack guard at `r14 + 16`) stops the walk.
- Miss classes (S1): `set-up order` only when the wanted `add $off,%r` ran in the field's set-up and a later
  directive replaced it; the right base with another offset is `other`; `padding` is assigned only to a head miss
  (inside the walk a `nop` is never a miss). `--summary` has `reached` per field: true up to the field where the walk
  stopped, false after it. A field with `reached: false` was not examined; its class says nothing. Resuming the walk
  after a miss is not done: the code of the missed field is not modelled, so no slot or register fact survives it,
  and the receiver / buffer slots could only be trusted again through a proof the generator does not have.
- Walker hazards checked in G4-F (each is modelled or stops the walk): partial-register writes (only `mov $i,%e..`,
  modelled as the zero-extending write of `kstep_movi`; every other 8 / 16 / 32-bit form stops); `lea` with an index
  or rip operand stops; a store through any base other than rsp or the receiver stops (a store through a pointer
  derived from rsp has an unknown base); calls other than the four callees, and runtime calls outside a segment, stop;
  after a call block all registers except rsp / rbp / r14 are unknown; flags are never read from the walk state (a
  conditional jump in the span stops; the `je` of a call / segment window is inside its lemma); a load at a
  displacement that is not a tracked slot gives `unknown`. The walker relies on the separation of frame, receiver
  and buffer that a field composition / accept statement assumes; it does not check it.
- Not examined (S3): the head is fixed by position (`cmp $size,%rcx` at directive 9, `jne` at 10). Since G4-F2 the
  epilogue is examined (below); the `jbe` / `jne` targets of the head (stack growth, size error) are not.
- `kindcheck.py` rule 11 (S2): the hand example modules `Gen2Examples.lean`, `Gen3Examples.lean` are exempt by exact
  path (`HAND_EXAMPLES`; rule 11 only). `Gen4Examples.lean` is not exempt: its hand field compositions fail rules 4
  and 10c; no recorded command runs `kindcheck.py` on it.
- Tests: `p2dec_test.py` cases `g4f-*` (26): the seven unsafe review inputs refused, the eleven valid variants covered,
  head classes, frame register writes; `reached` checked on every `--gen4` case. Committed `Gen4*.lean`: unchanged
  (the fixed generator regenerates all 10 byte-identical).

### G4-F2 (review g4f-r1 M3 and a systematic pass; g4f2-r1 REQUEST_CHANGES, fixed in G4-F3)

- Head size (M3): the immediate of `cmp $size,%rcx` (directive 9) must equal the IR SSZ fixed size of the type (the
  sum of the IR field sizes, which must equal the container's IR `fixed_size`), as the default mode checks in
  `compose_read`. Else the head misses: exit 2, every field `reached: false`, class `other` (review inputs c34, d15, d16).
- Epilogue: after the last field event the walker follows the accept path (nops, labels, forward `jmp`) and accepts
  only `mov d(%rsp),%rax|%rbx`, `xor %eax,%eax`, `xor %ebx,%ebx`, then `add $F,%rsp; pop %rbp; retq` with the head's
  frame size F. Anything else (a store, a call, another frame size, and since G4-F3 a `jmp` to a label that is not in
  the file) could change a decoded field after its event: exit 2, `--summary` has `epilogue.status: not covered` and
  every field `reached: true`, not covered, class `other`. Until G4-F3 a `jmp` to a label outside the file was
  accepted (review g4f2-r1 M4: x01, x02, x03 were reported fully covered).
  Review input a34 (a store after the last field) is now refused; it was a recorded limit before.
- Callee vs IR field: a call block is emitted only when the callee is the IR field's own overlay callee (unchanged
  rule; now tested both ways on PendingPartialWithdrawal). The class is `set-up order` only when a later IR field
  has that callee, else `other`.
- The systematic table (every number / symbol the walker reads, and what it is compared with) is in the unit's
  hand-over, not in this file. Rows that rely on the IR: Go offsets (`offset_gc_amd64`) and SSZ offsets are the IR's
  claim; the walker compares the code with them, nothing compares them with the Go compiler's layout.
- Tests: `p2dec_test.py` cases `g4f2-*` (9) and `g4f-a34` changed to "refused"; 169/169. Committed `Gen4*.lean`:
  unchanged (10/10 byte-identical; 33/33 `regen_check.sh` SAME).

### G4-F3 (review g4f2-r1 M4 and fail-closed result logic; g4f3-r1 APPROVE on `0e775ac`, the H6 method freeze; open items S6–S9 in `REPORT.md` §11)

- M4: in the epilogue, a `jmp` to a label that is not in the file (`jmp runtime.abort`, `jmp *%rdx`, a tail `jmp` to
  another decoder) is an epilogue miss: exit 2, every field not covered, `reached: true`, class `other`.
- Fail-closed: `p2dec_gen4` returns a text (exit 0) at one place only, the `else` branch of one `try` around
  `_p2dec_gen4`, and only when three flags are set: `head_ok` (`g4_head` returned), `fields_complete` (the walk
  returned without a stop and the field events are 0..n-1 in IR order) and `epilogue_ok` (`g4_epilogue` returned
  the value `G4_EPI_OK`). `NoMatch` / `Partial` keep exit 2 / 3. Any other exception of any phase (also
  `SystemExit`; not `KeyboardInterrupt`) is exit 2 with every field not covered and `fail_closed` in the summary.
  The epilogue is now its own phase after the walk. A run whose walk stopped has `epilogue.status: not examined`.
- Not examined (recorded limits, review g4f2-r1): the return value (an epilogue without `xor %eax,%eax` /
  `xor %ebx,%ebx` is covered, so the nil error is not checked); the makeslice element type is the literal
  `lea type__+387072(%rip),%rax` of the development ELFs, and nothing in the walker says that symbol is the byte
  type (another offset is "new directive form"); `test %al,(%rax)` in the head is optional (a decoder without the
  nil check is covered); a duplicate label: the walker takes the first (label freshness is the premise
  `LabelsFresh`); the head `jbe` / `jne` targets.
- Tests: `p2dec_test.py` cases `g4f3-x01..x03` (refused) and `fc-*`: a harness monkeypatches the working-tree
  generator and injects an unexpected exception, a plain `G4Stop` and `SystemExit(0)` in the head, at every
  `g4_parse` / `g4_label_index` call of the walk (every field), at every theorem-text call and in the epilogue
  (also wrong return values), plus a walk that returns every field with a stop. No injection reaches exit 0.
  Committed `Gen4*.lean`: unchanged (33/33 `regen_check.sh` SAME).

### Review g4f3-r1 should-fix notes (added at integration INT6; documents only, the generator is unchanged)

- S7: on exit 3 the code after the stopping field is not examined; later code may overwrite a covered field
  (reviewer input p01: fields 0–1 covered, later code overwrites field 1). A partial output says nothing about that code.
- S8: `fail_closed` appears in the summary only when the result guard fires; head or epilogue exceptions and errors
  before the IR is read give exit 2 without that key.
- S6 (a `NoMatch` inside a phase can leave `covered = total` in a summary with exit 2; not reachable in the code as
  written) and S9 (a stale `--partial-out` file stays on exit 0 / 2; no summary on `KeyboardInterrupt`) need a
  generator change: open, not done.
