# BASELINE: portable handoff of the prysm-e2e research state

Every value below is copied from the named file in this tree. "not recorded" means no file in the tree holds it.
Paths are relative to `fv/kraken/` unless they start with `fv/` or `.claude/`. Current state: `REPORT.md` §11.
`e2e/` abbreviates `prysm/go1.26.10/e2e/`; `scal/` abbreviates `prysm/go1.26.10/e2e/scal/`.

## 1. Pins

| Pin | Value | Read from |
| --- | --- | --- |
| Reviewed research state | `a70492c` (integrations INT2 + INT3, int-r2 APPROVE: 0 must-fix, 6 should-fix); this file is in a later documents-only commit (int-r2 should-fix S2–S6) whose ancestry contains `a70492c`. Earlier reviewed state: `c3c56a1` (int-r1 APPROVE) | `prysm/FINDINGS.md` checkpoint deltas (last entry), `HISTORY.md` |
| Reviewed streams | T-9 `154944e` (t9-r1 APPROVE), SG-1 `da3f233` (sg1-r1 APPROVE), merges `e56063c`, `63ef3b9` | `prysm/go1.26.10/e2e/scal/RESULT.json` `integration_s15` |
| Reviewed streams after this file was first written | H3 hold-out `75166e4` (h3-r1 APPROVE), ENC `ad15fbc` (enc-r1 APPROVE), both on base `dda707c`; merges `500571c`, `c10daf9` (integration INT2; reviewed by int-r2 APPROVE on `a70492c`) | `scal/RESULT.json` `integration_int2` |
| Reviewed local state (this branch, after INT4) | stream `claude/ssz-fv-h4` at `fae7d6f` (h4-r1 APPROVE; it contains G2-L `6c62a49` g2l-r1 APPROVE, G2-G `cd47028` g2g-r1 REQUEST_CHANGES documents only, G2-F `eacf0fb` g2f-r1 APPROVE); merge `56e0c88` has the same tree id as `fae7d6f`. The INT4 documents commit after the merge is NOT yet reviewed | `scal/RESULT.json` `integration_int4`, `H4.review_h4_r1` |
| Published | `71161fa` only (the earlier documents head of this branch, pushed as branch `ssz-fv-reuse-milestone` of the `syjn99` fork). GEN2, H4 and INT4 are local only; nothing newer is published | user record; no file in the tree pins a remote |
| scal method freeze (H4) | `eacf0fb4c03bf4b34ecf8b7a7705297998c848f7` (15 blob ids, the `lean/E2eScal` and `lean/Fk` tree ids) | `scal/HOLDOUT-OPENED` `H4.method_freeze` |
| scal method freeze (H3) | `dda707c77e9c2168cb778d13624b32fe87e07caa` (7 blob ids and the `lean/E2eScal` tree id) | `scal/HOLDOUT-OPENED` `H3.method_freeze` |
| Generator (`sszgen/`, `ssz/`) | `698c2025a73a296b55b95744a8408f3b03b2546b` (`syjn99/ssz-gen-fixes`, merge base `2d0150b`) | `prysm/go1.26.10/MANIFEST.md` §1, `TOOLS.md` |
| scal method freeze (H1, H2) | `56dfc27a6b0c7890105bd16971e0d33bbcd9980e`; `scalgen.py` blob `78e3339…`; SG-1 extended it afterwards | `scal/RESULT.json` `method_freeze`, `units.sg1-extension` |
| Prysm source | `ab15ff70c72a568c870b2de662474685a95de294` (slice + `ssz-size`), generated in a temporary tree only | `prysm/go1.26.10/MANIFEST.md` §1 |
| Go (e2e target) | `go version go1.26.10 linux/arm64`, cross-compiled | `prysm/go1.26.10/build-ids.txt` |
| Build flags | `GOOS=linux GOARCH=amd64 GOAMD64=v1 CGO_ENABLED=0 go build -p 2 -tags purego -trimpath` | `prysm/go1.26.10/build-ids.txt` |
| e2e ELF sha256 | `c6403c02a110ffd6fe6d31a3c89cd395ac457b5d62e60e2e611b8ab9a8dd911e`, 23486009 bytes; second build with empty GOCACHE: same sha256 and build ID | `prysm/go1.26.10/build-ids.txt`, `MANIFEST.md` §2 |
| e2e nm / objdump sha256 | nm `88ee8b9a…40ac` (2017324 bytes), full objdump `580b0da9…4a47` | `prysm/go1.26.10/e2e/e2e.json` `link_check_inputs`, `build-ids.txt` |
| Older Go 1.26.3 artifacts | `go1.26.3 darwin/arm64, GOAMD64=v1`; ELF `9c850c97066b9d33d6e4c5ef0a385dcbe2c984ae774a527cdedd18d2b72ac501`; `ssz/` tree id `92bba071…` (a tree id, not a commit) | `link/out/build-ids.txt` |
| Kraken | `6064eecbb730a1152aa6ed891a155d3a92a4f298`, AeneasVerif/kraken main (not a PR branch) | `lean/lake-manifest.json`, `TOOLS.md` |
| EthLib | `862185680cf23ccf54d44eb25b63b26c5020597b` | `lean/lake-manifest.json` |
| Lean | `leanprover/lean4:nightly-2026-09-21`; dump header `lean=4.36.0-nightly-2026-09-21 githash=ca39d2bc…` | `lean/lean-toolchain`, `prysm/go1.26.10/e2e/axioms-gate.json` |
| Pilot OPT-R1 (pilot ELF only; not the e2e baseline) | generator `ca191bb0c573830126dd017bd71a801f90038573` (branch `claude/ssz-gen-opt-r1`, parent `698c202`, NOT merged here; opt-in flag `--reserve-marshal`, default off); ELF `3ef7ac890ba1a797fb90877b84ad1a6ffe0ac283f77c10b09ffb2c8cd7b7f602`, 23486305 bytes, same Go and flags; stream `5821b19` (review opt-r1-r1 APPROVE), merge `83e0b6a` (integration INT3; reviewed by int-r2 APPROVE on `a70492c`) | `prysm/go1.26.10/opt-r1/MANIFEST.md` §1–2, `opt-r1/build-ids.txt` |

Where the binaries and link tables are:

- e2e ELF (Go 1.26.10) and its nm file: NOT in the tree (size). Rebuild: `prysm/go1.26.10/MANIFEST.md` §4. Check the rebuilt file against the sha256 above.
- e2e link tables in the tree: `prysm/go1.26.10/e2e/link/` (Checkpoint, Epoch), `e2e/ad/link/` (AttestationData, Slot, CommitteeIndex), `e2e/bh/link/` (BeaconBlockHeader, ValidatorIndex), `e2e/e1/link/` (Eth1Data). Each has `RESULT`, `norm/*.S`, `data/`. `e2e/link/target.objdump` is the filtered objdump.
- Prysm-wide Go 1.26.10 table: `prysm/go1.26.10/link/RESULT`. Go 1.26.3 ELF, nm, objdump: in the tree at `link/out/`.
- Go 1.26.3 theorems do not transfer to the Go 1.26.10 ELF (`MANIFEST.md` §1). The e2e proofs use the Go 1.26.10 `.S` only (`REPORT.md` §11).

## 2. Layout and runtime assumptions

- Receiver layout from `prysm/ir/ir-mainnet.json` `go_fields` (gc amd64 rules of `go/types`), not from the ELF `abi.Type` (`REPORT.md` §11).
- Runtime contracts are hypotheses, not proved: `MakesliceC`, `MemmoveC` (non-overlapping ranges only), `GrowsliceC`, `ConvT64C`, `NewobjectC`, `FmtErrorfWC`, `FmtErrorfDDC` (`CONTRACTS.md` §1–3; instances in `prysm/go1.26.10/e2e/RUNTIME-1.26.10.md` §2).
- They were re-read in Go 1.26.10 runtime source: unchanged. Source text only; the compiled runtime code is not compared (`RUNTIME-1.26.10.md` §1, §3).
- Each contract has a scratch stack window `S` and a spill size; the frame `F` is preserved (`CONTRACTS.md` §2).
- Premises: stack guard (`guard < rsp`, or `guard + N < rsp` for the large-frame form of `E2eScal.lea_cmp_be_false`), `runtime.writeBarrier = 0`, heap budget, label freshness, global addresses, initialised `ssz.Err*` words (`REPORT.md` §11 conditions 1–2; `CONTRACTS.md` §4).
- The morestack path is excluded by the stack-guard premise. GC during a call is outside every contract (`CONTRACTS.md` §3).
- X15 is not assumed zero on the encoder paths: bytes 8–31 of the temps are existential (`scal/RESULT.json` T-9 unit).
- T-7 is deferred: `GrowsliceC` gives no lower bound on the heap left after a call (`prysm/FINDINGS.md` T-7).

## 3. Coverage (type × function × path)

K = kernel-checked theorem (axioms standard). X = executable or differential only. N = NOT proved.
Module path is `lean/<Namespace>/<Module>.lean`. Sources: `prysm/go1.26.10/e2e/e2e.json`, `REPORT.md` §11, `scal/RESULT.json`.

| Type / function | Path | State | Theorem (namespace) |
| --- | --- | --- | --- |
| Epoch.UnmarshalSSZ | accept; length reject | K | `E2e.ep_unmarshal_accept_main`, `ep_uacc_holds`; `ep_unmarshal_reject_len_main` |
| Checkpoint.UnmarshalSSZ | accept; size reject; spec | K | `E2e.cp_e2e_accept_main`, `cp_e2e_reject_size_main`, `cp_e2e_accept_spec_k`, `cp_e2e_reject_complete` |
| Checkpoint.MarshalSSZTo | fast path; `ErrBytesLength` reject; spec | K | `E2e.cp_e2e_marshal_main`, `cp_e2e_marshal_reject_main`, `cp_e2e_marshal_spec_k` |
| Checkpoint.MarshalSSZTo | first growslice; second grows; reject after growslice | K | `cp_e2e_marshal_grow_main`, `cp_e2e_marshal_grow2_main`, `cp_e2e_marshal_reject_grow_main` |
| Checkpoint.MarshalSSZTo | first grows, then (A) / (B) return | K | `cp_e2e_marshal_grow_any_sharp` (A), (B) |
| Checkpoint.MarshalSSZTo | (C): run after the second growslice call when the heap left is below the budget (T-7) | N (X: differential only) | `cp_e2e_marshal_grow_any_sharp` and the covers end at the call entry |
| Checkpoint.SizeSSZ; decode→encode | size; composition | K | `cp_e2e_size_main`; `cp_e2e_unmarshal_then_marshal` (`⋆ True` remainder) |
| Slot, CommitteeIndex .UnmarshalSSZ | accept (function specs) | K | `E2eAd.sl_unmarshal_accept_main`, `ci_unmarshal_accept_main` |
| Slot, CommitteeIndex .UnmarshalSSZ | length reject | N | — (only `E2e.ep_unmarshal_reject_len_main` and `E2eScal.vi_unmarshal_reject_len_main` exist for the primitives) |
| AttestationData.UnmarshalSSZ | accept; size reject; spec | K | `E2eAd.ad_e2e_accept_main`, `ad_e2e_reject_size_main`, `ad_e2e_accept_spec_k` |
| AttestationData.MarshalSSZTo | all paths | N (not started, A4–A6) | — |
| ValidatorIndex.UnmarshalSSZ | accept (generated); length reject | K | `E2eScal.Gen.vi_unmarshal_accept_main_g`, `E2eScal.vi_unmarshal_reject_len_main` |
| BeaconBlockHeader.UnmarshalSSZ | accept; size reject; spec; two wraps | K | `E2eScal.Bh.bh_e2e_accept_main`, `bh_e2e_reject_size_main`, `bh_e2e_accept_spec_k`; `bh_e2e_{slot,vi}_err_unreachable` |
| BeaconBlockHeader.MarshalSSZTo | fast path (`len + 112 ≤ cap`, three roots of length 32) | K | `E2eScal.Bh.bh_e2e_marshal_main`, `bh_e2e_marshal_spec_k`, witness `WitBhM` |
| BeaconBlockHeader.MarshalSSZTo | three length rejects with `len + 112 ≤ cap` | K (ENC stream, enc-r1 APPROVE at `ad15fbc`) | `E2eScal.Bh.bh_e2e_marshal_reject{1,2,3}_main`, witness `WitBhMR`; block `E2eScal.enc_reject_tail` |
| BeaconBlockHeader.MarshalSSZTo | every growslice branch; length rejects with `cap < len + 112`; morestack | N | — (X: 6 growslice + 6 reject differential cases, not the proved path) |
| Eth1Data.UnmarshalSSZ | accept; size reject; spec | K (hand) | `E2eScal.E1.e1_e2e_accept_main`, `e1_e2e_reject_size_main`, `e1_e2e_accept_spec_k` |
| Eth1Data.MarshalSSZTo | fast path (`len + 72 ≤ cap`, two roots of length 32) | K (ENC stream, enc-r1 APPROVE at `ad15fbc`) | `E2eScal.E1.e1_e2e_marshal_main`, `e1_e2e_marshal_spec_k`, witness `WitE1M`; block `E2eScal.enc32_call` |
| Eth1Data.MarshalSSZTo | every growslice branch; two length rejects; morestack | N | — |
| BlobIdentifier.UnmarshalSSZ (hold-out H3) | accept; size reject; spec; reject_complete | K (BlockRoot segment generated, rest hand; h3-r1 APPROVE at `75166e4`) | `E2eScal.Bi.bi_e2e_accept_main`, `bi_e2e_reject_size_main`, `bi_e2e_accept_spec_k`, `bi_e2e_reject_complete` |
| BlobIdentifier.UnmarshalSSZ (GEN2, development set) | accept, same statement as `Bi.bi_e2e_accept_main` (`_type` identity) | K (2/2 segments generated; composition generated and by hand; GEN2 unit G2-G; reviewed g2g-r1 / g2f-r1; in-sample) | `E2eScal.Gen.bi_e2e_accept_main_gc` (generated), `E2eScal.G2.bi_e2e_accept_main_g2` (hand over generated segments) |
| DepositMessage.UnmarshalSSZ (hold-out H3) | accept; size reject; spec; reject_complete | K (WithdrawalCredentials segment generated, rest hand; h3-r1 APPROVE at `75166e4`) | `E2eScal.Dm.dm_e2e_accept_main`, `dm_e2e_reject_size_main`, `dm_e2e_accept_spec_k`, `dm_e2e_reject_complete` |
| DepositMessage.UnmarshalSSZ (GEN2, development set) | accept, same statement as `Dm.dm_e2e_accept_main` (`_type` identity) | K (3/3 segments generated; composition generated and by hand; GEN2 unit G2-G; reviewed g2g-r1 / g2f-r1; in-sample) | `E2eScal.Gen.dm_e2e_accept_main_gc` (generated), `E2eScal.G2.dm_e2e_accept_main_g2` (hand over generated segments) |
| Eth1Data.UnmarshalSSZ (GEN2, development set) | accept, same statement as `E1.e1_e2e_accept_main` (`_type` identity) | K (3/3 segments and composition generated; GEN2 unit G2-G; reviewed g2g-r1 / g2f-r1; in-sample) | `E2eScal.Gen.e1_e2e_accept_main_gc` |
| BlobIdentifier, DepositMessage: MarshalSSZTo, SizeSSZ, HashTreeRoot | all paths | N (out of H3 scope) | — |
| Deposit_Data.UnmarshalSSZ (hold-out H4) | accept (statement = independent hand statement `H4.dd_accept_stmt`); size reject; spec; reject_complete | K (result (S) 3/4: PublicKey, Amount, Signature segments generated, raw; WithdrawalCredentials hand lemma `H4.bytes32dec_seg_nop`; result (C) refused, composition by hand; h4-r1 APPROVE. PublicKey and Amount are near-in-sample (DepositMessage fields); Signature is the only out-of-sample covered field; the missed field is a near-in-sample 32-byte shape) | `E2eScal.H4.dd_e2e_accept_main`, `dd_e2e_reject_size_main`, `dd_e2e_accept_spec_k`, `dd_e2e_reject_complete`; witnesses `WitDdA`, `WitDdR` |
| PendingPartialWithdrawal.UnmarshalSSZ (hold-out H4) | size reject; reject-side spec; reject_complete (spec side) | K (result (S) 0/3, result (C) refused; h4-r1 APPROVE). `pw_e2e_reject_complete` is a spec-side fact only (EthLib rejects → size ≠ 24); the two callee error returns are not excluded | `E2eScal.H4.pw_e2e_reject_size_main`, `pw_e2e_reject_size_spec`, `pw_e2e_reject_complete`; witness `WitPwR` |
| PendingPartialWithdrawal.UnmarshalSSZ (hold-out H4) | accept (hand statement `H4.pw_accept_stmt`); callee error paths | N (accept: not proved, H4 attempt bound) | — |
| PendingPartialWithdrawal.UnmarshalSSZ (development data since GEN3) | accept (hand statement `H4.pw_accept_stmt`, unchanged) | K (GEN3 unit G3-L, after the hold-out, in-sample; not yet reviewed). This row supersedes the accept part of the row above; the callee error paths stay N | `E2eScal.H4.pw_e2e_accept_main` (over `calldec_seg`, `callarg_*_seg`, `u64dec_rr_seg`; callees through `vi_uacc_holds`, `ep_uacc_holds`); witness `WitPwA.pw_accept_runs` |
| PendingPartialWithdrawal.UnmarshalSSZ (GEN3 generator, development set) | accept, statement `H4.pw_accept_stmt` (unchanged; `_type` identity with `pw_e2e_accept_main`) | K (3/3 fields generated by `p2dec --gen3`, raw `Gen3PwDec.lean`; composition by hand; `--compose` refused: callee fields; GEN3 unit G3-G, in-sample; not yet reviewed) | `E2eScal.H4.pw_e2e_accept_main_g3` (`PwAcceptG3.lean`) |
| Deposit_Data.UnmarshalSSZ (GEN3 generator, development set) | accept, statement `H4.dd_accept_stmt` (`_type` identity) and kind `decAcceptKind` (`_kind`) | K (4/4 fields and the composition generated, raw `Gen3DdDec.lean`, `Gen3DdAccept2.lean`; GEN3 unit G3-G, in-sample; not yet reviewed) | `E2eScal.Gen.dd_e2e_accept_main_g3` |
| BeaconBlockHeader.UnmarshalSSZ (GEN3 generator, development set) | accept, same statement as `Bh.bh_e2e_accept_main` (`_type` identity) | K (5/5 fields generated, raw `Gen3BhDec.lean`; composition by hand; GEN3 unit G3-G, in-sample; not yet reviewed) | `E2eScal.Bh.bh_e2e_accept_main_g3`, `bh_e2e_head_g3g` (`BhAcceptG3.lean`) |
| AttestationData.UnmarshalSSZ (GEN3 generator, development set) | field segments only | K for 3/5 fields (Slot, CommitteeIndex, BeaconBlockRoot; raw partial `Gen3AdDecPartial.lean`); Source / Target (nested `*Checkpoint`) not covered | `E2eScal.Gen.ad_g3dec_*` |
| Deposit_Data, PendingPartialWithdrawal: MarshalSSZTo, SizeSSZ, HashTreeRoot | all paths | N (out of H4 scope) | — |
| SyncCommitteeMessage.UnmarshalSSZ (hold-out H5) | accept (statement = independent hand statement `H5.sm_accept_stmt`); size reject; spec; reject_complete | K (result (S) 2/4: Slot, Signature generated, raw; BlockRoot and ValidatorIndex by hand lemmas; result (C) refused, composition by hand; near-in-sample by kind; not yet reviewed) | `E2eScal.H5.sm_e2e_accept_main`, `sm_e2e_reject_size_main`, `sm_e2e_accept_spec_k`, `sm_e2e_reject_complete`; witnesses `WitSmA`, `WitSmR` |
| PendingConsolidation.UnmarshalSSZ (hold-out H5) | accept (statement = independent hand statement `H5.pc_accept_stmt`); size reject; spec; reject_complete | K (result (S) 1/2: SourceIndex generated, raw; TargetIndex by hand (`calldec_nop_seg`); result (C) refused; near-in-sample by kind; not yet reviewed) | `E2eScal.H5.pc_e2e_accept_main`, `pc_e2e_reject_size_main`, `pc_e2e_accept_spec_k`, `pc_e2e_reject_complete`; witnesses `WitPcA`, `WitPcR` |
| SyncCommitteeMessage, PendingConsolidation: callee error paths; MarshalSSZTo, SizeSSZ, HashTreeRoot | all paths | N (out of H5 scope) | — |
| SyncCommitteeMessage.UnmarshalSSZ (GEN4 mechanisms, development data since H5) | accept, statement `H5.sm_accept_stmt` (unchanged; the theorem's type is that abbrev) | K (GEN4 unit G4-L, in-sample; not yet reviewed). BlockRoot, ValidatorIndex and Signature through the window / step lemmas; an executed walk of the proof term (`G4DepCheck.lean`) does not reach `bytes32dec_seg_rax`, `sm_vi_arg` or `calldec_nop_seg`; head, nil-error spills and the Slot theorems as in the H5 proof | `E2eScal.H5.sm_e2e_accept_g4` (`SmAcceptG4.lean`) |
| PendingConsolidation.UnmarshalSSZ (GEN4 mechanisms, development data since H5) | accept, statement `H5.pc_accept_stmt` (unchanged; the theorem's type is that abbrev) | K (GEN4 unit G4-L, in-sample; not yet reviewed). TargetIndex through seven step theorems and the call-block window with the `nop`; head, epilogue and the SourceIndex theorems as in the H5 proof | `E2eScal.H5.pc_e2e_accept_g4` (`PcAcceptG4.lean`) |
| MarshalSSZ, HashTreeRoot, HashTreeRootWith of every type (Checkpoint included); SizeSSZ of every type except Checkpoint | all paths | N (outside the e2e function set) | — (`e2e/CALLGRAPH.md` §4, FINDINGS AU-09) |
| decoder `fmt.Errorf` wraps | unreachable_mc (conditional skip, not reject coverage) | K | `E2e.cp_e2e_epoch_err_unreachable`, `E2eAd.ad_e2e_*_err_unreachable` |
| hand-written `primitives` methods | every method and path not in a K row above (FINDINGS O2 counts "the other 23 methods" after Epoch only; it predates the Slot, CommitteeIndex and ValidatorIndex decoder rows above) | N | `prysm/FINDINGS.md` O2 |
| runtime callees (makeslice, memmove, growslice, convT64, newobject, fmt.errorf) | contract bodies | N (hypotheses) | `CONTRACTS.md` |
| Checkpoint.MarshalSSZTo, pilot ELF `3ef7ac89…f602` only (old proofs are about the old ELF) | fast (`len + 40 ≤ cap < 2^63`); reject in that range; grow (`len ≤ cap < len + 40`); reject on grow; spec (fast path) | K; covers unframed (they end in `⋆ True`) | `E2e.OptR1.cpo_marshal_main`, `cpo_marshal_reject_main`, `cpo_marshal_grow_main`, `cpo_marshal_reject_grow_main`, `cpo_marshal_spec_k`; covers `cpo_marshal_cover`, `cpo_marshal_reject_cover` |
| Pilot ELF `3ef7ac89…f602` only | framed covers; nil receiver; morestack; every other function of the pilot ELF (AttestationData encoder included) | N (nil receiver: X, differential only) | — |

Every growslice branch except the Checkpoint ones above is NOT proved. No encoder is complete; there is no full coverage claim.
Rows marked "ENC stream" are kernel-checked on the branch `claude/ssz-fv-enc-reuse` (base `dda707c`); review enc-r1 approved `ad15fbc`. Both encoders: fast path only; the BeaconBlockHeader rejects only under `len + 112 ≤ cap`.
Go-value checks: a Lean predicate exists for Checkpoint only (`E2e.cpGoValue`, module `lean/E2e/GoVal.lean`); BeaconBlockHeader, Eth1Data, AttestationData, BlobIdentifier, DepositMessage, Deposit_Data and PendingPartialWithdrawal receivers have none (`REPORT.md` §11).
No run on x86-64 hardware (`REPORT.md` §11 condition 3).
OPT-R1 rows (integration INT3): kernel-checked on the pilot ELF only, review opt-r1-r1 APPROVE on `5821b19`. The e2e ELF rows above are unchanged and do not transfer.
In the pilot binary's function the second growslice call does not exist, so path (C) does not occur there. T-7 itself is unchanged and deferred (`GrowsliceC` form unchanged).
Pilot reject proof for `8 ≤ spare < 40` depends on `GrowsliceC`, `MemmoveC` and the heap budget; the e2e reject theorem (`spare ≥ 8`) is contract-free.
Direct witnesses exist for `cpo_marshal_main`, `cpo_marshal_cover`, `cpo_marshal_reject_cover`; the other four theorems are reached through the cover witnesses only.

## 4. Method evidence (as recorded)

- H1 (frozen method `56dfc27`): ValidatorIndex decoder accept generated, BeaconBlockHeader decoder with 3 generated root segments. One out-of-sample case per type; no generator-superiority or causal speed-up claim (`scal/RESULT.json` `claims_and_limits`).
- H1 encoder: the BeaconBlockHeader fast path was not proved at H1 time; 9 attempts failed (3 in session 10, 6 in session 11) (`REPORT.md` §11, `prysm/FINDINGS.md` T-9).
- H2 (historical, before SG-1): the frozen generator ran once on Eth1Data: exit 2, 0 bytes, 0 of 2 root fields (job 393; `scal/RESULT.json` `H2`, FINDINGS SG-1). The decoder was then proved by hand.
- SG-1 extension: offset-0 template `rootdec_seg_z` and `scalgen.py p2dec` form, developed on Eth1Data after both hold-outs were opened. Eth1Data is in-sample and the hold-out is contaminated for it. Output 2 of 2 fields; no generalisation claim (`scal/RESULT.json` `units.sg1-extension`, `scal/CONTAMINATION.md` §8).
- H3 (frozen method `dda707c`, opened in `782a41b`): one generator run per type, exit 0, raw output unedited; coverage 1/2 (BlobIdentifier) and 1/3 (DepositMessage) fields; the inline uint64 fields and the 48-byte PublicKey by hand (FINDINGS SG-2). Two types, one touch; no superiority, general-automation or speed-up claim (`scal/RESULT.json` `H3`, `scal/CONTAMINATION.md` §11). Reviewed: h3-r1 APPROVE on `75166e4` (next bullet); merged tree reviewed by int-r2 APPROVE on `a70492c`.
- H3 review (correction, integration INT2): h3-r1 APPROVE on `75166e4`; the reviewer reran the generator once per type in scratch (byte-identical), 12 of 33 negatives and the link check. Reading A3 (class N counts own fields) was fixed after the candidate list was visible and before any method code was opened; under the other reading class N is `ProposerSlashing` (`scal/CONTAMINATION.md` §11).
- H3 limits: generator 1 of 2 and 1 of 3 fields; SG-2 open (no inline uint64 template, no 48-byte segment). One touch of two types; no generalisation, superiority or causal speed-up claim. No witness instantiates the `*_accept_spec_k` premise `Pm` (as for Eth1Data and BeaconBlockHeader).
- GEN2 (unit G2-G, development set after H3; review g2g-r1 REQUEST_CHANGES, documents only, closed by G2-F): opt-in `scalgen.py p2dec --gen2` covers Eth1Data 3/3, BlobIdentifier 2/2, DepositMessage 3/3 fields (raw output unedited); `--compose` emits the accept theorems; their only statement check is the `_type` identity with the hand theorems (no kind; a hold-out type has no hand theorem). Hand lines (non-blank, non-comment, whole module): BlobIdentifier 210 → 120 (hand composition) → 0 (generated), DepositMessage 464 → 155 → 0. No generalisation claim before H4 (`scal/RESULT.json` unit `gen2`).
- GEN2 after review g2g-r1 (REQUEST_CHANGES, documents only) and fix unit G2-F (g2f-r1 APPROVE on `eacf0fb`, the H4 method freeze; its S1–S4 `kindcheck.py` changes are open proposals, not done): "0" means hand lines in the generated module only. The hand reference theorems stay and are the only statement check of a composed theorem; the G2-L lemma modules are hand-written once (824 lines); code module, Desc, spec alignment, reject, witnesses, link tables and negatives are outside the number. DepositMessage without `DmSeg0`: 255 → 155 (−39.2 %); accept proof body only: 80 → 62 and 120 → 93 (−22.5 % each). Not covered: delegated overlay fields (Slot, Epoch, ValidatorIndex: compiled as calls), byte vectors of other sizes, uint64 with displacement 0, nested containers, lists, bitfields, bool / other uints, encoders. Fields typed Slot / Epoch / ValidatorIndex are not covered, so most consensus containers are outside GEN2 as it stands (reviewer runs: BeaconBlockHeader 3/5, Checkpoint 1/2, AttestationData 1/5). G2-F: kindcheck accepts a `_type` identity only for a composed theorem and never against a generated name; `--gen2 --partial-out` writes a valid Lean module (`Gen2BhDecPartial.lean`, BeaconBlockHeader 3/5, in-sample, builds unedited; `kindcheck.py --partial` exit 3).
- H4 (frozen GEN2 method `eacf0fb`, opened in `9d338fa`; h4-r1 APPROVE on `fae7d6f`): one (S) and one (C) generator run per type, raw output unedited. Development-set coverage (in-sample): Eth1Data 3/3, BlobIdentifier 2/2, DepositMessage 3/3, whole proofs generated. Hold-out coverage: Deposit_Data 3/4 fields, of which PublicKey and Amount are near-in-sample and Signature is the only out-of-sample covered field; the missed WithdrawalCredentials is a near-in-sample 32-byte shape that failed on a padding `nop` (SG-3). PendingPartialWithdrawal 0/3 (overlay-typed fields compiled as calls; rax-receiver interleaved uint64 read). Whole-proof generation (`--compose`) refused for both types. The Deposit_Data accept path was proved by hand over the 3 generated segments and one new hand lemma; the PendingPartialWithdrawal accept path is NOT proved (attempt bound). Hand lines: Deposit_Data accept path 336 without the statement module `H4Stmt.lean` (112, both types); H3 values 210 / 464 include their statements, so the numbers are not like for like; tools are outside every count. Negatives 30/32; some cases were replaced or rerun after the first run (`scal/RESULT.json` `H4.review_h4_r1`). Two types, one touch; no generality, transfer or speed-up claim.
- ENC (development data, not a hold-out; enc-r1 APPROVE on `ad15fbc`): encode block `E2eScal.enc32_call` (the memmove call site) and reject block `E2eScal.enc_reject_tail`. Reuse is PARTIAL: proof lines per BeaconBlockHeader root site 56 / 66 / 68 via the block against 61 / 71 / 73 by hand, block 18 lines; the straight-line steps stay per site (FINDINGS ENC-1). `Eth1Data.MarshalSSZTo` and `BeaconBlockHeader.MarshalSSZTo`: fast path only; BeaconBlockHeader length rejects only under `len + 112 ≤ cap`. No speed-up claim (`scal/RESULT.json` unit `enc-reuse`).
- T-9: cause = the `simp` + `omega` proof of the large-frame guard branch fails in the kernel under the memory limit (4.88 GiB under `lean -M 5000`); the costly subterm was not profiled; the `2^64 − 32` literal is an inference. Fixed by the lemma `E2eScal.lea_cmp_be_false`; then 5 attempts, 2 failed (`scal/RESULT.json` T-9 unit).
- AU-07 (open): `E2eScal.P2EncCp` (Checkpoint encode template) costs 986.0 s for one `lake env lean` (n = 1, review fix-r1), against 4.5 s for the hand proof. Three attempts (953–973 s `omega`) gave no speed-up; the slow call was not located (`e2e/opt1/AU-07.json`).
- Witness-build measurement (AU-06, `e2e/opt1/AU-06.json`): four witness modules 1636.8 s → 165.3 s after the `wit_split_n` tactic.
  Measured: one gated `lake env lean` per module, same method before and after, wall time on a shared machine, n = 1 each.
  Limits: n = 1, so the run-to-run spread is not known; a per-file `lean` run is not a full build. Audit numbers from another method are not comparable. No negative case targets these modules.
- OPT-R1 pilot (one function, one binary; integration INT3): the generator option reserves `len + 40` once in `Checkpoint.MarshalSSZTo`. Correctness-preserving re-validation shown: 7 theorems, 8 witnesses, link check PASS, Go differential 31/31 (arm64, Go semantics only). Speed-up NOT shown in general (mixed result).
  Benchmarks (linux/arm64 only, medians of n = 20, `opt-r1/bench/bench-summary.json`): B2 nil dst allocs 2 → 1, 56 → 48 B, ns faster but run-dependent; B3 cap 8: the expected 2 → 1 allocs did not hold (2 = 2); B5 fast-path reuse 1.92 → 2.19 ns (+14 %); B8 1000 appends allocs 18 → 17, ns +3.4 %; B9 invalid Root, spare 16: allocs 0 → 1, ns worse; B1 `MarshalSSZ()` and B7 nested AttestationData unchanged.
  Limits: the reviewer's spot rerun (B2, B5, B8, B9 only, not the full protocol) reproduced B5 +12.6 % and the alloc and B/op counts; ns of allocating cases varied up to about 35 % between rounds, so no fixed percentage for B2 is quoted. No x86-64 run. Negatives 21/23 at 300 s; the two `tail_fit` store mutants, rerun once at 900 s, are `outside` and `timeout_heartbeat`: not passes (`opt-r1/RESULT.json` `negatives.s3_rerun_int3`).

## 5. Reproduction (commands relative to the repository root)

The heavy-job gate and the 6 GiB memory cap used in these runs are local infrastructure; they are NOT in the repository.
Run heavy jobs one at a time and under a memory limit. Commands in `REPORT.md` §11 "재현" and `prysm/go1.26.10/MANIFEST.md` §4 are the full list.

```sh
(cd fv/kraken/lean && lake build E2e E2eAd E2eScal)    # E2eScal.P2EncCp alone took 986 s (n = 1)
(cd fv/kraken/lean && lake build --no-build E2e E2eAd E2eScal)   # expect exit 0 after the build
python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run <out.json> <dump.tsv>   # WRITES <out.json>; give a scratch path unless you mean to update the committed record
GOROOT=$(go env GOROOT) go test -count=1 ./ssz/ ./sszgen/... ./fv/kraken/semtest/
python3 -I -B fv/kraken/gen/scal/kindcheck.py --selftest
python3 -I -B fv/kraken/gen/e2e/negative.py <negcases.json> <work> <result.json> <case-id>   # one job per case
```

Expected at the earlier reviewed state `c3c56a1`: `axioms-gate.json` `verdict` PASS, `declarations` 3483, `theorems` 2923, `modules` 115, `nonstandard` {}, `sorryAx` [].
On the ENC branch alone (enc-r1 APPROVE): `declarations` 3813, `theorems` 3223, `modules` 123 (`scal/RESULT.json` unit `enc-reuse`).
Both `axioms_gate.py run <out.json> <dump.tsv>` and `axioms_gate.py check <dump.tsv> <out.json>` overwrite the JSON argument (review b1-r1 S7). The committed record is `prysm/go1.26.10/e2e/axioms-gate.json`.
After the integration INT2 (H3 + ENC, merge `c10daf9`): `declarations` 4142, `theorems` 3467, `modules` 143, hand list 315 (`scal/RESULT.json` `integration_int2`). Reviewed by int-r2 APPROVE on `a70492c`.
After the integration INT3 (OPT-R1, merge `83e0b6a`): `declarations` 4519 (= 4142 + 377 `E2e.OptR1`), `theorems` 3813, `modules` 154, hand list 315 (OptR1 names are not in the hand lists). Reviewed by int-r2 APPROVE on `a70492c`.
After GEN2 (units G2-L and G2-G; later reviewed: g2l-r1 APPROVE, g2g-r1 REQUEST_CHANGES documents only): `declarations` 4720 (= 4519 + 106 G2-L + 95 G2-G, decl drift ADDED only), `theorems` 3994, `modules` 170, hand list 391 (command: `axioms_gate.py run`, committed record `prysm/go1.26.10/e2e/axioms-gate.json`). State at that time: not yet reviewed; superseded by the reviews named in this row.
After G2-F (g2f-r1 APPROVE on `eacf0fb`): `declarations` 4726 (= 4720 + 6 in `Gen2BhDecPartial`, decl drift against the g2g-r1 dump: ADDED 6 only), `theorems` 4000, `modules` 171, hand list 397 (command: `python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run fv/kraken/prysm/go1.26.10/e2e/axioms-gate.json <dump.tsv>`, Lean env, one gated job).
After H4 and the integration INT4 (merge `56e0c88`): `declarations` 5007 (= 4726 + 281 H4, decl drift ADDED only; INT4 vs the h4-r1 dump: 0 changed, 0 removed, 0 added), `theorems` 4204, `modules` 189, hand list 443. H4 reviewed by h4-r1 APPROVE; INT4 not yet reviewed.
After GEN3 (units G3-L and G3-G; not yet reviewed as a whole; G3-L reviewed by g3l-r1 APPROVE on `f5c5f52`): `declarations` 5463 (= 5007 + 330 G3-L + 126 G3-G; decl drift vs the int4-r1 dump: ADDED 456 only), `theorems` 4536, `modules` 207, hand list 582 (command: `python3 -I -B fv/kraken/gen/e2e/axioms_gate.py run <out.json> <dump.tsv>`; record `prysm/go1.26.10/e2e/axioms-gate.json`).
After H5 (not yet reviewed): `declarations` 5841 (= 5463 + 378 H5; decl drift vs the g3g-r1 dump: ADDED 378 only), `theorems` 4826, `modules` 228, hand list 582 (unchanged: `gen/scal/AxiomsScal.lean` is frozen for H5; the gate enumerates every declaration).
The count comes from `decl_dump.lean` (`.claude/skills/maintaining-methodical-fv/scripts/`) over the roots E2e, E2eAd, E2eScal, run by `axioms_gate.py`.
`scal/RESULT.json` `integration_s15.executed` lists the other expected results (negatives 36/36 T9, 15/15 SG1; regen SAME 6/6; `p2dec_test.py` 10/10).
A cold build from an empty `.lake` was not run in any reviewed unit (`scal/RESULT.json` `integration_s15.not_run`).

Portability caveats:

- Rebuild `.lake` on the new machine with the pinned toolchain; do not copy it. `lake build --no-build` checks the trace, `lake env lean` does not (AU-05).
- Go differentials ran natively on linux/arm64: they check Go semantics, not the amd64 ELF (`REPORT.md` §11).
- The link check needs the ELF and nm file, which are not committed; rebuild them first and compare sha256.
- Historical cost and negative records hold absolute paths of the original machine (`TOOLS.md` "알려진 위반"). They are records, not inputs.
- `MANIFEST.md` §3–4 names local tree paths and environment files of the original runs; the commands use them as placeholders.
- The Prysm tree for differentials is temporary and not in the repository (`MANIFEST.md` §3).

## 6. Open findings (`prysm/FINDINGS.md`)

| ID | One line |
| --- | --- |
| T-7 | `GrowsliceC` gives no lower bound on the heap left; the run after the second growslice call is not proved |
| T-9 (residue) | fast paths proved for BeaconBlockHeader and (ENC stream, enc-r1) Eth1Data; BeaconBlockHeader length rejects proved only for `len + 112 ≤ cap` (ENC stream); growslice branches and morestack of both encoders, and the Eth1Data length rejects, not proved |
| ENC-1 | six root-append sites have six instruction texts; the shared encode block is the call site (`enc32_call`), the steps before it stay per site (reuse partial); reviewed (enc-r1) |
| ENC-2 | the BeaconBlockHeader encoder writes earlier fields to `dst[len:]` before a later length reject (class of C-1); reviewed (enc-r1) |
| SG-2 | frozen generator covers 32-byte `[]byte` vectors only: H3 coverage 1/2 and 1/3 fields; GEN2 (`p2dec --gen2`, reviewed g2g-r1 / g2f-r1): addressed on the development set (3/3, 2/2, 3/3, in-sample); H4 (h4-r1): did not transfer unchanged (SG-3) |
| SG-3 | H4 hold-out, frozen GEN2 generator: Deposit_Data 3/4 (a `nop` before `callq runtime.makeslice` in the WithdrawalCredentials segment), PendingPartialWithdrawal 0/3 (delegated overlay calls; an interleaved inline uint64 form); `--compose` refused both | recorded; proposals P-H4-1..3 not done (`scal/CONTAMINATION.md` §16); reviewed (h4-r1 APPROVE); 2 of the 3 covered Deposit_Data fields are near-in-sample |
| P-H4-1..3, kind | open generator proposals, not done (method changes, approval needed): tolerate a padding `nop` before `callq runtime.makeslice`; the rax-receiver interleaved inline uint64 form; overlay-typed fields compiled as calls; a kind for composed statements |
| g2f-r1 S1–S4 | open checker proposals for `kindcheck.py`, not done: comment-free rule 6a; `--partial` n against the theorems present; reject n ≠ m in the default mode; selftest controls |
| SG-1 | extended after both hold-outs; no hold-out claim for the extension; DepositCount has no template |
| AU-01 | gate lock is not FIFO; user decision: measure first |
| AU-07 | `P2EncCp` `omega` cost not located; the encode template is net-negative in build time |
| AU-14 | policy tool limits (decl_dump roots, stale_olean); deferred |
| D1 | generator IR key for nested container fields; generator not changed |
| K2 | Kraken parser has no `bsr`; Kraken request |
| C-1 | Checkpoint encoder writes the epoch before the root-length test; known behaviour, review pending |
| T-3, T-4 | local workarounds (data reader copy, `eaddr` macro); review pending |
| T-1, T-2 | decoder closing tactics above 6 GiB (split at `L_b4`) and `ecancel` AC step (re-elaboration workaround); review pending |
| T-6, T-8 | one witness host per file; `ecancel` with `⋆ emp` and AC forms of witness memory (workarounds); review pending |
| AU-09 | hold-out limits: `SizeSSZ` excluded from H1; H2 = Eth1Data `UnmarshalSSZ` / `MarshalSSZTo` only (user decision) |
| O2 | 23 hand-written `primitives` methods have no proof |
| OPT-R1 | pilot: reserve option for `Checkpoint.MarshalSSZTo` on a separate ELF; re-validated, mixed benchmark result; user decision 2026-11-11: not adopted (evidence kept, option off); §8 |

## 7. Test contract for a new type

A new-type unit is done only with all of these, each recorded with its job and exit code:

1. An independent Desc written from consensus-specs before the checker Desc is printed (FINDINGS NF-10).
2. Codec equality of that Desc with the checker Desc (`*_serialize_checker`, `*_deserialize_checker`).
3. Accept and reject theorems on the target `.S`, with exact frames; spec alignment against EthLib (`*_spec_k`).
4. Witnesses that satisfy every premise: empty, one, maximum for variable lengths; Go-valid receivers (`fv/AGENTS.md`).
5. A link check PASS for the new functions on the pinned ELF (`e2e/<type>/link/RESULT`).
6. Negative cases, one gated job each: controls pass, mutants fail inside the target; no timeout or wrong-target counted.
7. A Go-value check: a Lean predicate, or a Go differential stated as Go semantics only.
8. Axioms gate PASS and a decl drift with only ADDED rows against the reviewed base dump.
9. A list of NOT proved paths. Never "complete".

## 8. OPT-R1 pilot: open user decisions (review opt-r1-r1)

Each needs an explicit yes from the user. Source: `opt-r1/RESULT.json` `review_opt_r1_r1`.
User decision 2026-11-11: the pilot is NOT adopted. The evidence stays in the tree; the option stays off (default). This closes U5. U1–U4 and U6 were not decided separately.

- U1 Item 6: with an invalid Root and `8 ≤ spare < 40` the new code allocates one block (old: none) and does not write the caller's spare (old: C-1 write). Returned values unchanged. That range of the reject proof depends on `GrowsliceC`, `MemmoveC` and the heap budget.
- U2 `cap < 2^63` on `cpo_marshal_reject_main` and `cpo_marshal_reject_cover` (signed reserve compare; Go guarantees `cap ≤ 2^48`).
- U3 Guard premise `guard + 24 < rsp`; frame 0x90; spill slots rsp+8 and rsp+24 are now written.
- U4 `head_fast` took 4 compiles against a bound of 3.
- U5 Keep the opt-in option? Gains: allocs 2 → 1 when dst has fewer than 40 spare bytes. Costs: fast path +12–14 % (B5), error path 0 → 1 alloc (B9), B8 ns not better.
- U6 No push or publication of either branch (`claude/ssz-gen-opt-r1`, the research branch). Not requested, not done.
