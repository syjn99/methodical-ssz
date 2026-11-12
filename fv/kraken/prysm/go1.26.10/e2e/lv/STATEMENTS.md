# STATEMENTS: list/vector hand theorem statements (T1, T2)

These statements are committed before the proofs.
They are not changed after the commit.
If a change is necessary, add it with a new name and record the reason. The original statement stays.
Lean source: `lean/E2eList/StmtSa.lean`, `lean/E2eList/StmtSc.lean`.
Definitions that the statements use: `lean/E2eList/Defs.lean`, `lean/E2eList/Desc.lean`, `lean/E2eList/Data.lean`, `lean/E2eList/Code.lean`.
Model for the shape: `E2eScal.H4.dd_accept_stmt` and its four specification theorems (`DdReject.lean`, `DdSpecK.lean`).

## 1. List

| Name | Path | Claim |
| --- | --- | --- |
| `sa_accept_stmt` | SyncAggregate accept (machine code) | It returns nil on a 160-byte input. The two fields are new blocks and are equal to the input slices. It uses 160 bytes of heap |
| `sa_reject_size_stmt` | SyncAggregate size reject (machine code) | If rcx ≠ 160, it returns the two words of `ssz.ErrSize`. `R` stays the same |
| `sa_accept_spec_stmt` | SyncAggregate accept (specification) | If EthLib accepts `bsA` as `v`, there is a `g` with `g.toValue = v` and `bsA = psaEnc g`. The machine code writes `g` to the receiver |
| `sa_reject_size_spec_stmt` | SyncAggregate size reject (specification) | If `bs.size ≠ 160`, EthLib rejects and the machine code returns `ssz.ErrSize` |
| `sa_reject_complete_stmt` | SyncAggregate reject completeness | All inputs that EthLib rejects have `size ≠ 160` |
| `sc_accept_stmt` | SyncCommittee accept (machine code) | It returns nil on a 24624-byte input. Pubkeys is a new `[][]byte` of length 512. Element i is equal to input slice i. It uses 36912 bytes of heap |
| `sc_reject_size_stmt` | SyncCommittee size reject (machine code) | If rcx ≠ 24624, it returns the two words of `ssz.ErrSize` |
| `sc_accept_spec_stmt` | SyncCommittee accept (specification) | If EthLib accepts, there is a `g : PSc`. The machine code writes `g` to the receiver |
| `sc_reject_size_spec_stmt` | SyncCommittee size reject (specification) | If `bs.size ≠ 24624`, EthLib rejects and the machine code returns `ssz.ErrSize` |
| `sc_reject_complete_stmt` | SyncCommittee reject completeness | All inputs that EthLib rejects have `size ≠ 24624` |

This unit has no statements for `IndexedAttestation`.

## 2. Premises

These are the common premises of all machine-code statements.

- Code location: `XUnmarshal.IsInfixAt Host.prog k` and `LabelsFresh XUnmarshal k`.
- Stack guard: `guard.toNat < rsp.toNat`. It blocks the morestack path.
- Write barrier: the 4 bytes of `runtime.writeBarrier` = 0. The piece is in `h_mem`.
- Memory: `h_mem` gives all slots as separate pieces. They are the return slot, rbp slot, spill slots, locals, spill, return slot, scratch `S`, guard, `Heap avail`, input, receiver slots, write barrier and the rest `R`.
- Accept size: `rcx = 160` or `rcx = 24624`. The specification statements have `rcx.toNat = bsA.size`.
- Heap: `160 ≤ avail` or `36912 ≤ avail`.
- Contract hypotheses: `MakesliceC Heap e2eU8Type_addr 1 S`, `MemmoveC S`. SyncCommittee also accepts `MakesliceC Heap lvSliceType_addr 24 S`.
- The size reject has no contract hypothesis. It calls no callee.

## 3. Postconditions

Accept (machine code):

- pc = return address, rax = 0, rbx = 0, rsp = entry rsp + 8, rbp and r14 are entry values.
- The return slot, rbp slot, the two spill slots (entry rax, rbx), guard, input, `state`, write barrier and `R` stay the same.
- The local x − 16 is the last field pointer. The SyncCommittee x − 32 and x − 24 are 8 bytes, and their values are not specified.
- For the 24-byte spill and the scratch `S`, only the length is specified.
- The return slot is the return address of the last memmove (SyncAggregate `addrOf (k + 68)`, SyncCommittee `addrOf (k + 101)`).
- The heap is `Heap (avail − 160)` or `Heap (avail − 36912)`.
- SyncAggregate receiver: `+8` = p1, `+16` = `+24` = 64, `+32` = p2, `+40` = `+48` = 96. bits at p1, sig at p2.
- SyncCommittee receiver: `+8` = A, `+16` = `+24` = 512, `+32` = pA, `+40` = `+48` = 48.
- SyncCommittee array: `lvHdrs 48 ps` at A (element headers `(ps[i], 48, 48)`), `lvElems ps pks` (pks[i] at ps[i]), agg at pA.
- There is no `⋆ True` tail. The full footprint is stated.

Size reject (machine code): pc = return address, rax = e0, rbx = e1, rsp + 8, rbp, r14. The rbp slot has the entry rbp, x + 16 has the entry rbx, and the rest stays the same.

Specification: accept is `∃ g, g.toValue = v ∧ bsA = enc g ∧ (machine-code postcondition)`.
The premise `Pm` gives the memory from the pieces of `g`, for all `g` with `bsA = enc g`.
This form is the same as `dd_e2e_accept_spec_k`.

## 4. Places with judgment

- The hand `Desc` copies the consensus-specs altair definition from memory. The repo has no copy of the source text.
- The producer `Desc` (`lv/desc/`) was printed after the hand `Desc` was written. Only the field names differ (visual check). There is no theorem yet.
- The `state` slot is not read. It still stays as `ast`, to record that it is unchanged (same as `dd_accept_stmt`).
- The end values (511, 1533) of the SyncCommittee loop locals x − 32 and x − 24 are not stated. They are dead slots, so only the length is stated.
- Reject completeness is a pure specification statement. The fact that the machine code has no other error return is a judgment from a read of the `.S`.
- The judgment is that the esz 24 instance of `MakesliceC` is not a new form. The form accepts esz as a parameter.
- The stack guard premise is `guard < rsp`. The contract does not have the callee check the guard, so no margin was added (same as `dd_accept_stmt`).
