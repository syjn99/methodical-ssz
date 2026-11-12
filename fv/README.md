# Formal verification of the generated SSZ code

This directory holds machine-checked proofs about the code that the generator of this repository emits.
The generator is `sszgen/` with its runtime library `ssz/`.
SSZ (Simple Serialize) is the serialization format of the Ethereum consensus layer.
Each project is one subdirectory. The only project is `kraken/` (see `kraken/README.md`).

The agent and process rules are in `../AGENTS.md` and `AGENTS.md`.
This file gives the design principles. It does not repeat those rules.

## 1. What a proof says

A proof is about the compiled x86-64 machine code of one Go method of one type.
The methods are the decoder `UnmarshalSSZ`, the encoder `MarshalSSZTo` and `SizeSSZ`.
The hash tree root methods are not in the scope yet.

- The object is the machine code in one ELF file. The Go source is not the object.
- The Go compiler is not trusted and is not evidence. Its output is the thing that we examine.
- The specification is the SSZ `serialize` and `deserialize` functions of EthLib, a Lean library of Ethereum specifications.
- A `Desc` is the EthLib description of one SSZ type. Each proved type has one `Desc`.
- The semantics is Kraken, a model of x86-64 instructions in Lean 4.

A decoder theorem says this: on an input that EthLib accepts, the code returns nil and the receiver holds the decoded value.
On an input that EthLib rejects, the code returns the error that the Go source names.
An encoder theorem says that the output bytes are the EthLib serialization of the receiver.

The proofs have two uses.
First, a proof that cannot close shows a place where the code and the specification can disagree.
Second, after a change that makes the generated code faster or smaller, the same statements check that the code is still correct.

## 2. The three sources of a theorem

Every theorem depends on three pinned sources.

| Source | What is pinned |
| --- | --- |
| Specification | The EthLib commit, and the `Desc` of each type |
| Target | The generator commit, the source of the types, the Go version, the build flags and the sha256 of the ELF |
| Semantics | The Kraken commit and the Lean toolchain |

A theorem is about the exact instruction sequence of one compiled function and the exact data bytes that it reads.
A different compiler, a different flag or a different generator gives different instructions.
Thus a change of one source makes the theorems unchecked until they build again against the new pin.
A proof about one ELF never transfers to another ELF. A new binary needs new proofs.

## 3. Trust base

The proofs assume these items. They do not prove them.

- The Lean kernel, and the Kraken model of each instruction. No test compares Kraken with a real x86-64 CPU.
- The EthLib specification itself.
- The conversion from the ELF to Lean text. A converter writes assembly files, and a Lean command reads them.
  The link check (see `kraken/link/README.md`) compares that text with the ELF bytes. The converter and the reader stay trusted.
- The runtime callee contracts. A contract is a Lean hypothesis that describes a Go runtime function.
  Examples are memory allocation, slice growth, memory copy and error formatting.
  The contracts come from a reading of the Go runtime source. No proof shows that the compiled runtime satisfies them.
- The hash function, when hash tree root proofs start. It stays a contract until a separate project proves it.
- The Go memory layout of the receiver types. It comes from the `go/types` size rules, not from the ELF.

Behavior of other clients and the output of the Go compiler are never evidence.

## 4. Done for one function of one type

One function of one type is done only when all of these items exist.

1. **Accept theorem.** It runs the machine code from entry to return on every accepted input.
2. **One theorem for each reject path.** Each error return in the code has its own theorem.
   An error path without a theorem is listed as not proved.
3. **Specification alignment.** A theorem connects the machine result to EthLib.
   Accept means that EthLib accepts and the receiver holds the EthLib value. Reject means that EthLib rejects.
4. **Witness.** A concrete machine state satisfies all premises of the main theorem.
   Without a witness, the premises can be contradictory and the theorem says nothing.
   For a variable length, the witnesses cover the empty value, one element and the maximum.
5. **Negative tests.** A mutation of one instruction or of the statement must make the designated theorem fail.
   An unchanged control must pass. This shows that the theorem depends on the code that it names.
6. **Link check.** The included code and data are the bytes of the pinned ELF.
7. **Go value check.** The witness receiver is a valid Go value of that type.
8. **Axioms and drift checks.** See section 6.
9. **List of paths not proved.** For example, the stack growth path and the garbage collector write barrier path.

Never write "complete" for a function that has an item in its list of paths not proved.

## 5. Statement rules

- Write the statement before the proof, and commit it. A later change gets a new name and a written reason.
- Never weaken a statement to make a proof close. Weakening stops the work, and the work is reported.
- Give every size an explicit range. Do not quantify over all sizes.
- Give every memory region as a separate fragment with its owner. The regions are the input, the receiver, the stack slots, the heap and the frame.
- The frame `R` is the rest of the caller memory. The postcondition keeps it unchanged.
- Give each runtime call an explicit stack window: the scratch bytes below the return slot.
- The postcondition keeps the input, the frame, the return address, `rsp + 8` and the preserved registers `rbp` and `r14`.
- Do not end a postcondition with `⋆ True`. A `⋆ True` remainder says nothing about the rest of memory.
  If a theorem has one, its documentation says so, and a framed version states the exact memory.
- A contract hypothesis states its size range, the runtime memory that it owns, the frame and the stack window.
- Label freshness and global addresses are premises of the theorem. The link check confirms them on the real ELF.

## 6. How the checks decide

- **Build.** The Lean kernel accepts every proof.
- **Axioms.** Every declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. Any other axiom or `sorryAx` fails.
- **Statement drift.** A declaration dump of the new tree is compared with a reviewed dump.
  A changed or removed statement is drift. Drift needs a reason that a reviewer accepts.
- **Negative tests.** A mutant passes the suite only if it fails inside its designated theorem.
  A timeout or an error outside that theorem is not a pass.
- **Link check.** It passes only when every function and every data file agrees with the ELF.

A timeout or an out-of-memory kill is a result. It is never a pass.
A check that did not run is reported as "not run".
The commands are in `kraken/README.md`.

## 7. Findings

A proof that cannot close is a candidate finding.
A candidate is confirmed only by a concrete input, a theorem or a Go test that shows the behavior.
Record each finding in `kraken/FINDINGS.md`, with its place, its effect and its state.

A fix to the generator or to the runtime library needs explicit user approval.
A fixed generator gives a new ELF, and a new ELF needs new proofs.
Change the Go regression test and the Lean reject theorem in the same change.

## 8. Pointers

- `../AGENTS.md`: roles, prohibitions and approval boundaries.
- `AGENTS.md`: the rules for all work under this directory.
- `kraken/README.md`: the project, its pins and its commands.
- `kraken/FINDINGS.md`: the findings of the project.
