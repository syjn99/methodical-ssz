# CONTRACTS: treatment of callees and globals (Kraken hypothesis form)

Target: SizeSSZ, MarshalSSZTo and UnmarshalSSZ of the 9 Go 1.26.3 test types. At fix 3, the target also had `ssz.ValidateBitvector`.
The definitions are in `lean/Fk/Contracts.lean` and `lean/Fk/FunSpecs.lean`.
The change history is in `HISTORY.md`.

On 2026-11-12, commit `84a4747` removed most theorems and all witnesses of the 9 test types. Tag `archive/fv-before-workflow` holds them.
It also removed `lean/Fk/Vbl.lean` (ValidateBitlist contracts), `lean/Fk/Vbv.lean` (ValidateBitvector specification) and `lean/Fk/RtVbl.S`.
The contract definitions in `Fk/Contracts.lean` and `Fk/FunSpecs.lean` stay, because kept `Fk` modules and the Prysm proofs use them.
The callers, formats and spill slots below are those of the Go 1.26.3 target code. They do not say that a theorem about that caller still exists.

Classification:

- **(a) Proof target**: we prove it by running the machine code with the Kraken semantics.
- **(b) Contract**: a hypothesis of the theorem. It quantifies over all machine states, return addresses and frames `F`.
- **(c) Excluded under a precondition**: a premise of the theorem blocks that path. We prove the fact that it blocks the path.

## 1. Callees

The Witness column named `Fk` witness modules (`Fk/Wit*.lean`, `Fk/Witness.lean`). They were removed on 2026-11-12. "Removed" marks those cells.

| Callee | Calling function (path) | Classification | Form | Model | Witness |
| --- | --- | --- | --- | --- | --- |
| `runtime.makeslice` | FixedVec, ListU64, Checkpoint, AttestationData UnmarshalSSZ, ListC.UnmarshalSSZ (element pointer array) | (b) | `MakesliceC` | `bump_makeslice` (esz 8), `bump_makeslice1` (esz 1) | Removed |
| `runtime.memmove` | Unmarshal and Marshal of FixedVec, Checkpoint, AttestationData, BitL | (b) | `MemmoveC` | `rt_memmove` | Removed |
| `runtime.growslice` | All MarshalSSZTo (capacity too small), BitL.UnmarshalSSZ (`append([]byte{}, buf[4:]...)`) | (b) | `GrowsliceC` | `rt_growslice` (esz 1) | Removed |
| `runtime.newobject` | Nested, AttestationData, ListC UnmarshalSSZ, the three ListC error objects, the `ssz.ValidateBitvector` error object | (b) | `NewobjectC` | `bump_newobject16/24/32` | Removed |
| `runtime.convT64` | ListU64.UnmarshalSSZ (alignment, excess), ListC.UnmarshalSSZ (alignment, element count) | (b) | `ConvT64C` | `rt_convT64` | Removed. The two ListC paths had no theorem |
| `fmt.errorf`, 0 arguments | ListC.UnmarshalSSZ (offset errors zero, past, tail) | (b) | `FmtErrorfNilC` | `rt_errorf_nil` | Removed |
| `fmt.errorf`, `%w` | BitVec decoder `"J: %w"`, BitL decoder and encoder `"B: %w"`, ListC element error `"Items: %w"` | (b) | `FmtErrorfWC` | `rt_errorf_w` | Removed |
| `fmt.errorf`, `%d %w` | ListU64.UnmarshalSSZ (alignment, excess) | (b) | `FmtErrorfDWC` | `rt_errorf_dw` | Removed |
| `fmt.errorf`, `%d %d` | ListC.UnmarshalSSZ element offset order (`lc_reject_offset_order_main`, removed on 2026-11-12) | (b) | `FmtErrorfDDC` | `rt_errorf_dd` | Removed |
| `target.Scalars.UnmarshalSSZ` | Nested.UnmarshalSSZ | (a) function specification | `ScUAccC` | `sc_uacc_holds` | Removed |
| `target.ListU64.UnmarshalSSZ` | Nested.UnmarshalSSZ, ListC.UnmarshalSSZ (for each element) | (a) function specification | `LuUAccC` | `lu_uacc_holds` (needs `MakesliceC`) | Removed |
| nil branch after `runtime.newobject` | ListU64 reject (the case where `fmt.errorf` returned nil) | (c) | rax ≠ 0 of `FmtErrorfDWC` blocks it | | |
| `runtime.gcWriteBarrier1/2` | All decoders | (c) | Premise `runtime.writeBarrier` = 0. We prove that the code reads the flag and skips it | | |
| `runtime.morestack_noctxt.abi0` | All functions with a frame | (c) | Premise `g.stackguard0` (r14 + 16) < rsp. We prove that `jbe` does not branch | | |
| `runtime.panicBounds` | FixedVec, ListU64 UnmarshalSSZ loops | (a) | We prove for each iteration that the bounds check does not branch (`lu_iter`, `fv_iter`) | | |

Rows removed on 2026-11-12: `ssz.ValidateBitlist` (`ValidateBitlistC`, `ValidateBitlistErrC`), `ssz.ValidateBitvector` (`VbvAccC`, `VbvPadC`) and the ListU64 short-input function specification `LuURejShortC`.
At fix 3, `joint_models` (`Fk/Regress.lean`) satisfied 11 contracts together in one Host and one heap, and `tools/RegressFix2.lean` applied it again.
Both files were removed on 2026-11-12. Tag `archive/fv-before-workflow` holds the removed rows and files.

## 2. Conditions for each contract

All contracts assume a Go 1.26.3 ABIInternal (amd64) call.
The return address is at rsp.
`S` is the number of scratch bytes below the return slot.
A spill is a register argument slot immediately above the return slot. The callee can write to it.

| Contract | Argument conditions | Resource budget | Stack window | Preserved and conclusion |
| --- | --- | --- | --- | --- |
| `MakesliceC Heap ty esz S` | rax = ty, `len ≤ cap = cnt`, `cnt < 2^63` | `esz·cnt ≤ avail`, `esz·cnt ≤ maxAlloc` | scratch S, spill 24 | rsp + 8, r14, rbp, `F`. It removes a zero-filled block of `esz·cnt` bytes from `Heap` |
| `MemmoveC S` | rcx = n, n bytes of source and destination, disjoint | None | scratch S, no spill (asm `$0-24`) | rsp + 8, r14, rbp, source, `F`. Destination = source |
| `GrowsliceC Heap ty esz S` | `0 < esz`, rsi = ty, `num ≤ newLen`, `oldLen = newLen − num ≤ oldCap < newLen` | `nc = nextSliceCap newLen oldCap` (Go `nextslicecap`), `2·esz·nc + 8192 ≤ avail ≤ maxAlloc = 2^48` | scratch S, spill 40 | rsp + 8, r14, rbp, rbx = newLen, old block, `F`. `nc ≤ newCap`, new block = `old ++ tail`, `avail' + esz·newCap ≤ avail` |
| `NewobjectC Heap ty sz S` | rax = ty | `sz ≤ avail` | scratch S, spill 8 | rsp + 8, r14, rbp, `F`. A zero-filled block of `sz` bytes |
| `ConvT64C Heap S` | All v. Precondition `StaticBox v` (if v < 256, the 8 bytes from 8v of the included ELF table `Fk.Data.staticuint64s`, read-only. They are = v by `staticBox_of_lt`) | `8 ≤ avail`. Conclusion `avail' + hb.length ≤ avail ≤ avail' + 8` | scratch S, spill 8 | rsp + 8, r14, `StaticBox v`, `F`. `BoxIn rax v hb` (static table or 8 heap bytes = v) and `Eq (hb.At rax)` |
| `FmtErrorfNilC S` | rdi = 0, no `%` in the format, format byte fragment | No allocation | scratch S, spill 40 | rsp + 8, r14, format, `F`. rax = 0 |
| `FmtErrorfWC Heap fs RO MsgIn S` | Format `fs` fixed (`bvFmtJ`, `blFmtB`, `lcFmtItems`), rdi = rsi = 1, argument array `ity ++ e`, `ErrObj e sp msg`, `Eq (hm.At sp)`, read-only `RO`, `MsgIn sp msg hm` | `fs + msg + 8192 ≤ avail`. Conclusion `avail' ≤ avail` | scratch S, spill 40 | rsp + 8, r14, format, arguments, `ity`, error object, `hm`, `RO`, `F`. rax ≠ 0 |
| `FmtErrorfDWC Heap fs tw S` | Format `fs` fixed (`luFmtTooBig`, `luFmtMis`), rdi = rsi = 2, argument array `tw ++ bx ++ ity ++ e` (tw = `Fk.Data.intType_addr`, `type:int`), `BoxIn bx v hb`, `StaticBox v`, `Eq (hb.At bx)`, `ErrStr e sp msg` | `fs + 20 + msg + 8192 ≤ avail` | scratch S, spill 40 | Same as above. Includes the box resources. rax ≠ 0 |
| `FmtErrorfDDC Heap fs tw S` (limit: `StaticBox v1 ⋆ StaticBox v2` cannot be satisfied if v1 = v2 < 256. In that case, Go convT64 gives the same pointer. The order reject is not affected because e < s) | Format `fs` fixed (`lcFmtOrder`), rdi = rsi = 2, argument array `tw ++ bx1 ++ tw ++ bx2` (tw = `Fk.Data.uint64Type_addr`), two `BoxIn`, `StaticBox v1`, `StaticBox v2`, two sets of box bytes | `fs + 40 + 8192 ≤ avail` | scratch S, spill 40 | Same as above. Includes the box resources. rax ≠ 0 |

The rows `ValidateBitlistC S` and `ValidateBitlistErrC Heap S` were removed on 2026-11-12 with `Fk/Vbl.lean`.

Constants that the link check fixes (`link/check.py`):

- (g) `vbvFmt`, `bvFmtJ`, `blFmtB`, `vblMsgE`·`vblMsgZ`·`vblMsgB`, `luFmtTooBig`·`luFmtMis`, `lcFmtZero`, `lcFmtShort`.
- (h) The abi.Type of `luTW` = `type__+49184` has Size_ 8, Kind_ 2 (int). The abi.Type that itab+8 points to has Kind_ 22 (pointer). `runtime.staticuint64s` is the 2048 bytes of uint64 0..255.

## 3. Abstract models and Go refinement

We keep two kinds of proofs apart.

- **Abstract model proofs.** The `rt_*` and `bump_*` theorems show that small assembly programs on the Kraken semantics satisfy the contracts.
  They are the evidence that the contracts are not contradictory.
  At fix 3, `joint_models` also showed that one Host and one heap can satisfy several contracts together. It was removed on 2026-11-12 (section 1).
- **Go refinement.** A proof that the real machine code of the Go 1.26.3 runtime satisfies the contracts. There is none.
  Every contract call is a trust item for real Go execution.

Trust items outside the form premises:

| Contract | Trust item | Reason |
| --- | --- | --- |
| `FmtErrorfWC`, `FmtErrorfDWC`, `FmtErrorfDDC` | The real allocation amount of Go (printer object, result string, `*fmt.wrapError` 32 bytes) is in the budget. No GC occurs during the call. The result object is not in the conclusion (only rax ≠ 0) | We did not model the allocation path of fmt and sync.Pool. The budget values come from reading the code |
| `FmtErrorfNilC` | If the format has no `%`, it returns nil without allocation (from reading Go 1.26.3 `fmt/errors.go`) | We did not prove the internal code of fmt |
| `MakesliceC`, `NewobjectC`, `GrowsliceC`, `ConvT64C` | They do not read the type descriptor. No GC occurs during allocation. Allocator failure is outside the theorems | There is no allocator or GC model |
| `MemmoveC` | It covers only ranges that do not overlap | The `⋆` of the caller excludes overlap. Go memmove also permits overlap |

## 4. Globals and runtime state

| Item | Treatment | Basis |
| --- | --- | --- |
| `ssz.Err*` (two words) | Separate fragment at the label address + value premises (e0, e1) | `link/check.py` (b) compares the address with the ELF `.symtab` |
| itab + 8 of `ssz.ErrX` | The reject path reads `*(e0 + 8)`. Premise: e0 ≠ 0, and that 8-byte fragment | A fact after package initialization (premise) |
| `runtime.writeBarrier` | Premise: 4 bytes = 0. It is in `F` during contract calls, so we assume that it does not change | False if the GC enters the mark phase during allocation |
| Stack guard | Section 1 (c). Stack growth of the callee is outside the contracts. We assume that the scratch `S` is sufficient | |
| X15 = 0 (Go ABI) | The reject paths do not assume it (we prove the `movups %xmm15` store as a store of an arbitrary value). At fix 3, only the ListC empty-list accept had it as a premise. That theorem was removed on 2026-11-12 | Go ABIInternal (amd64) guarantees it |
| Label freshness | Premise `LabelsFresh` of the theorems. For the real layout (`all.S`), `link/check.py` (c) checks it. For a concrete Host, the Lean theorems `Fk.Witness.hf5` and `hf198` checked it. `Fk/Witness.lean` was removed on 2026-11-12 | |
| Spill slots | The premise of the theorem takes those locations as separate fragments (ListU64 rsp − 136, FixedVec and BitVec rsp − 32, Checkpoint rsp − 40, AttestationData rsp − 48, ListC rsp − 224, Nested rsp − 96, BitL rsp − 120) | |

## 5. How contracts are hypotheses

A contract is a **hypothesis** of the theorem. It quantifies over all states, return addresses and frames.
At the call site, `eventually_trans` gives the postcondition of the contract, and the proof continues from an arbitrary state that satisfies it.

- There are no indexed havoc values (1a finding 7). If the code calls the same contract two times, the proof applies the same hypothesis to different states.
- If the result selects a path, a fact in the postcondition decides the branch. Example: rax ≠ 0 of `FmtErrorfDWC` decides the direction of `test %rax,%rax; jne`. If the postcondition does not give that fact, we prove both paths.
- The remaining risk is a contradiction in the contract itself. The form is not evidence of non-vacuity. Only the models and the witnesses are evidence.

## 6. Do the premises of the theorems hold at real Go callers?

| Premise | Go caller |
| --- | --- |
| Argument registers (rax = receiver, rbx/rcx/rdi = slice) | ABIInternal guarantees them |
| Receiver ≠ nil | Not guaranteed. A nil receiver panics in Go (`test %al,(%rax)`). If a separate fragment exists, we treat its address as mapped (Kraken `Effects.All` does not check access permissions) |
| Disjointness (`⋆`) of input, receiver, stack and output | Holds for usual Go values. We exclude aliasing (bytes in the receiver used as input) |
| Stack guard, write barrier 0 | Fast-path premises. Not a guarantee of a general call |
| bool byte ∈ {0, 1}, slice len ≤ cap < 2^63, object size, alignment and overlap | Invariants of Go values. The main theorems can permit wider states. The witnesses must be Go values. For the Go 1.26.3 witnesses, `lean/tools/wit/goval.py` checked them with `layout.json`. Both were removed on 2026-11-12 |
| Heap space (`avail`) | If the allocator fails, Go does not return normally. The theorems speak only about the success case |
