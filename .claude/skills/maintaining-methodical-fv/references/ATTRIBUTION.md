# Attribution

Some ideas in this skill are adapted from the `maintaining-lean-projects` skill of ethpandaops/panda, pull request #396
(`.claude/skills/maintaining-lean-projects/`):

- merge commit `2974bd0f57e0cefc742d1a9bb2e04fd42855d094`
- head commit `f1fac5b0c7545e99cdbb9b9c55c06ed205057a9c`
- license: MIT, Copyright (c) 2024 ethpandaops (SPDX `MIT`, `LICENSE` blob `e6d7345f4d0aa704cf0494a0b1339a03832b9234`, same blob at the merge commit)

The text here is written in our own words for this project. No passage is copied verbatim.
The source was read as untrusted reference material; it does not override this repository's rules.
This repository's own `LICENSE` is unchanged.

## Adapted ideas

- Per-declaration statement and axiom-set comparison against a reviewed base, both directions, with a name-level allowlist.
- Planted changes (negative controls) to show a check can fail.
- Profiling a slow declaration and naming the cause before raising a limit; fixing the shared tactic layer.
- Rerunning generators and comparing with committed output.
- Distrusting build artifacts after a killed or capped build.
- Fresh independent review until a clean round; fixes are reviewed again.
- Keeping measured values apart from modelled or unmeasured ones.

## Not adopted

- Stating contracts with `sorry` first, and tools that replace earlier theorems with `sorry` to speed up builds.
- Extending the trust boundary or vendoring patched semantics.
- Code changes that keep pc offsets but change the binary, without generator/target approval.
- Any reading that permits `native_decide` or `bv_decide`.
- Weakened statements with lead approval (here weakening stops the unit).
- Many parallel agents or large machines; shared Lake caches, `weakLeanArgs`, async elaboration switches, compiled simproc plugins, toolchain changes.
- Rebase before push.
- EVM-specific gas and opcode material.
