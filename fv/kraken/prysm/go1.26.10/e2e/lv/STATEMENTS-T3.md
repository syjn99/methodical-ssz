# STATEMENTS-T3: `IndexedAttestation.UnmarshalSSZ` hand theorem statements

These statements are committed before the proofs. They are not changed after the commit.
If a change is necessary, add it with a new name and record the reason.
Lean source: `lean/E2eList/StmtIa.lean`. Definitions used: `DefsIa.lean`, `DataIa.lean`, `CodeIa.lean`, `IncludeIa.lean`.
Design: `DESIGN-T3.md`.

## 1. List

| Name | Path | Claim |
| --- | --- | --- |
| `ia_reject_size_stmt` | size reject | If `len < 228`, it returns the two words of `ssz.ErrSize`. `R` stays the same |
| `ia_reject_offset_stmt` | offset reject | If `len ≥ 228` and `buf[0:4] = off ≠ iaOff`, it returns the two words of `ssz.ErrInvalidVariableOffset` |
| `ia_reject_misaligned_stmt` | alignment reject | If the offset is 228 and `(len − 228) % 8 ≠ 0`, it goes through convT64 and errorf (DWC) and returns with rax ≠ 0. The frame is exact |
| `ia_reject_toobig_stmt` | overflow reject | If the offset is 228, the alignment holds and `(len − 228)/8 > 2048`, it returns in the same form |
| `ia_accept_stmt` | accept | For all `n ≤ 2048`, if it gets `iaOff ‖ data ‖ sig ‖ ib(8n)`, it returns nil. Receiver = (A, n, n), `ib` at A. Data = new object (the content is the conclusion of `ad_e2e_accept_main`). Signature = (psig, 96, 96) = sig. Heap `8n + 432` |
| `ia_reject_size_spec_stmt` | size reject specification | If `bs.size < 228`, EthLib rejects and the machine code reaches the size reject conclusion |
| `ia_reject_offset_spec_stmt` | offset reject specification | If `bs.size ≥ 228` and `bs[0:4] ≠ iaOff`, EthLib rejects and the offset reject conclusion is reached |
| `ia_reject_misaligned_spec_stmt` | alignment reject specification | Under the alignment condition, EthLib rejects and the alignment reject conclusion is reached |
| `ia_reject_toobig_spec_stmt` | overflow reject specification | Under the overflow condition, EthLib rejects and the overflow reject conclusion is reached |
| `ia_accept_spec_stmt` | accept specification | If EthLib accepts `bsA` as `v`, there is a `g` with `g.toValue = v` and `bsA = piaEnc g`, and the machine code writes `g` to the receiver |
| `ia_reject_cases_stmt` | pure specification | An input that EthLib rejects satisfies one of the size reject, offset reject, alignment reject and overflow reject conditions |

## 2. Premises

- Code location and label freshness: `IaUnmarshal`. Accept also takes `AdUnmarshal`, `SlUnmarshal`, `CiUnmarshal`, `CpUnmarshal`, `EpUnmarshal`.
- Stack guard: `guard + 48 < rsp` for reject, `guard + 408 < rsp` for accept (the guard condition of the delegate included).
- Write barrier = 0 (accept). The reject paths do not read the write barrier.
- Accept input: `n ≤ 2048`, `len = 228 + 8n`, `len ≤ cap < 2^63` (the 266 bounds check and the 18–24 pointer computation).
- Contract hypotheses (all of existing forms): accept takes `MakesliceC lvU64Type 8`, `MakesliceC u8 1`, `MemmoveC`, `NewobjectC lvAdType 96` (scratch `Sd + 224`) and the five of the delegate (scratch `Sd`, `Sd + 96`). The alignment reject and the overflow reject take `ConvT64C`, `FmtErrorfDWC` (format `lvFmtMis`/`lvFmtTooBig`, `tw = e2eIntType_addr`).
- Error globals of the alignment reject and the overflow reject: first word = errorString itab (`he0`), the 8 bytes `ity` at itab + 8, `ErrStr e1 esp msg`, budget `fs + msg + 8220 ≤ avail`.

## 3. Postconditions

- Accept: pc = return address, rax = 0, rbx = 0, rsp + 8, rbp, r14. The exact frame (the 8-byte values of the five dead locals are not specified), the input, `state` and `R` stay the same. Return slot = `addrOf (k + 241)`. Heap `avail − (8n + 432)`.
- Size reject and offset reject: rax = e0, rbx = e1. Only the rbp slot and the rbx spill slot change.
- Alignment reject and overflow reject: rax ≠ 0. Argument array (32 bytes) = `type:int ‖ box ‖ ity ‖ e1`. Box `BoxIn bx v hb`, heap `avail' + hb.length ≤ avail`. Return slot = `addrOf (k + 117)` (alignment reject), `addrOf (k + 80)` (overflow reject).
- There is no `⋆ True` tail.

## 4. Places with judgment

- The first offset is stated as a 4-byte list and `iaOff` (= `[0xe4, 0, 0, 0]`). It is stated as bytes instead of a 32-bit integer.
- The elements are stated as one byte list (`ib`, length `8n`). The reason: the `[]uint64` array is a contiguous block. On the specification side, `u64Bytes g.idx` is that list.
- The heap premise of the accept specification is `bsA.size − 228 + 432 ≤ avail`. It is the same value as `8n + 432` (n = (size − 228)/8).
- The conclusions of the alignment reject and the overflow reject have no rbx (the data word of the error). The DWC contract does not give that value.
- The delegate error has no statement. It is not reached under the accept premises (`DESIGN-T3.md` section 2).

## 5. Statement correction after the freeze: the `_nz` of the alignment reject and the overflow reject (2026-11-12, user approval)

- The four frozen statements (`ia_reject_misaligned_stmt`, `ia_reject_toobig_stmt`, the two specification variants) cannot be proved as written. The verdict is N. They were not deleted or changed.
- Gap: directives 103–106 (alignment reject) and 66–69 (overflow reject) are `test %rcx,%rcx; je`. If the itab word `e0` of the error is 0, the code does not read the type word and passes 0. `FmtErrorfDWC` requires `ity` at that position. The Kraken `Host` puts labels at arbitrary addresses. Thus when the itab label is 0, that `je` cannot be refuted.
- Correction: the four statements in the new file `E2eList/StmtIaNz.lean` (`ia_reject_misaligned_nz_stmt`, `ia_reject_toobig_nz_stmt`, `ia_reject_misaligned_spec_nz_stmt`, `ia_reject_toobig_spec_nz_stmt`).
- Each correction adds only one premise `(he0nz : e0 ≠ 0)` to the source text. The script comparison shows 4 changed lines per definition (the old and new lines of the name line and the binder line).
- The corrected premise is stronger than the frozen statement. It is not the same statement.
- Precedent: `lu_reject_misaligned_main` (Go 1.26.3) of `Fk/LuRejectCall.lean` has both premises `he0 : e0 ≠ 0` and `hei : e0.toBitVec = (label "go_itab._errors.errorString_error").toBitVec`.
- In the real ELF, `e0` is the itab address `0xd28520`. Check (b) `go_itab._errors.errorString_error = 0xd28520` of `lv/link-t3/RESULT` ties the label to this address.
- This goes on the user decision list as "statement correction after the freeze".
