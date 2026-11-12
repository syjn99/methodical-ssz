# FINDINGS candidates (list/vector work)

This file is a candidate list for `prysm/FINDINGS.md`.
The existing ledger did not change.
The IDs are stable IDs.

| ID | First seen | Status | Evidence kind | Content |
| --- | --- | --- | --- | --- |
| LV-1 | link unit (logs 08, 66), after `9b805e0` | fixed (`93b3f2a`), review r4 approval | execution (X) | tool gap candidate in the negative displacement notation. It is not a production defect |

## LV-1

- Line 19 of the normalized `.S` of `IndexedAttestation.UnmarshalSSZ` is `lea 0xffffff1c(%rdi),%rdx`.
- `go tool objdump -gnu` writes the 32-bit displacement −228 as `0xffffff1c`.
- `link/conv.py` keeps that notation as is.
- x86-64 sign-extends the 32-bit displacement. The machine address is rdi − 228.
- Apple clang 21.0.0 rejects this line (`displacement 4294967068 is not within [-2147483648, 2147483647]`).
- Thus `check.py` (d) failed (log 08).
- The Kraken parser (`6064eec`) reads it as `disp := ↑4294967068`.
- It reads `lea -0xe4(%rdi),%rdx` as `disp := ↑(-228)` (log 66).
- A proof with this `.S` handles an address that differs from the machine.
- The other committed `.S` files do not have this form (`git grep '0xffffff..(%'`, result 0). The existing theorems are not affected.
- Fix location candidates (not done): `conv.py --norm` writes the displacement as a signed number. Or add a displacement range check to `check.py`.
- It is not known whether the LLVM of the earlier link checks accepted this notation.
- The full ELF objdump (`p1cbin-amd64.objdump`, sha256 `580b0da9…`) has 153 operands of the wrapped form (`grep -cE '0xffff[0-9a-f]{4}\(%'`).
- Those 153 are in 104 functions. The 104 are 67 UnmarshalSSZ and 37 MarshalSSZTo.
- This objdump file has 641 TEXT functions: UnmarshalSSZ 211, MarshalSSZTo 211, SizeSSZ 211, MarshalSSZ 6, `ssz.ValidateBitvector` 1, `ssz.ValidateBitlist` 1. There is no HashTreeRoot (review r2 M2).
- The wide pattern `0x[89a-f][0-9a-f]{7}\(%` gives 161. The 8 added ones are `lea` of the form `0xffd6xxxx(%r..)`. All 161 are in the same 104 functions (review r2 S3).
- The 222 committed `.S` files also do not have the wide pattern.
- Thus LV-1 is not a problem of IndexedAttestation only. If `conv.py --norm` makes the `.S` of those functions, the same notation remains. The effect per function was not counted.

## LV-1 fix (`93b3f2a`, user approval)

- `conv.py --norm` now writes an 8-digit displacement with the top bit set in signed form (`0xffffff1c(%rdi)` → `-0xe4(%rdi)`).
- Output of the full ELF before and after the fix: 104 changed files, 161 changed lines, 0 differences outside the displacement tokens (logs 103–105).
- The new output has 0 wrapped forms.
- The 7 committed `--norm` bundles of this ELF (37 files) and `link/norm` (136 functions) are byte-for-byte the same when made again (logs 106, 107).
- `opt-r1/link` is a different ELF, so it was not compared.
- The IndexedAttestation link is PASS for all of (a)–(f) in `lv/link-t3/` (log 111, BUNDLE `393eade6…`).
- Kraken reads the fixed line as `disp := ↑(-228)` (log 113).
- Review r4 approved this fix (`REVIEW-R4.md`).
- The fix does not handle the SIB form without a base (`0xffffff00(,%rcx,8)`) and the segment form without a base. This objdump has 0 of each (review r4 S9).
- Remaining candidates (not done): a displacement range check in `check.py`, a request that the Kraken parser reject out-of-range displacements.
