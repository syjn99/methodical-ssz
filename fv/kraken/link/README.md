# link: from the ELF to Lean, and the link check

The proofs read converted assembly text and data files, not the ELF.
The link check shows that this text and these files are the code and the data of the pinned ELF.
Paths in this file are relative to `fv/kraken/`. A command that starts with `fv/kraken/` runs from the repository root.

## 1. Programs

| Program | Task |
| --- | --- |
| `link/conv.py` | Converts `go tool objdump -gnu` output into one labeled `.S` file per function, plus `all.S` with all functions in address order |
| `link/data.py` | Writes one data file per ELF data item of the test target. With `--check`, it compares a new extraction with the tracked files |
| `link/check.py` | The link check. It writes the result file `RESULT` |
| `link/build.sh` | Builds the test target ELF and runs the steps above for it |

`conv.py` changes only what Kraken cannot read directly:

- A jump or call target becomes a label. Inside a function, the label is `L_<function>_<offset>`. Outside, it is the symbol name.
- A `disp(%rip)` operand becomes `symbol+offset(%rip)`.
- Symbol names get a short form that Kraken can parse.
- With `--norm`, multi-byte padding instructions become `nop`, and a zero SIB index `%riz` is dropped.
  A 32-bit displacement with the top bit set is written as a negative number.

The converter stops with exit 1 in these cases: a line without the GNU form, a gap between instructions, a branch into an instruction, or two symbols with the same short name.

## 2. What the link check proves

`check.py <outdir>` reads the ELF, the disassembly, the symbol listing, the `.S` files and the data files of one link set.

- **Code.** For each function, the symbol table gives its address and size. The disassembly covers that range with no gap.
  The disassembly bytes are the ELF bytes. An independent decoder (`llvm-objdump`) finds the same instruction boundaries.
  Each label `L_<function>_<offset>` sits before the instruction at that offset.
- **Global labels.** Each call target and each `symbol+offset(%rip)` names a symbol of the ELF. The original displacement gives the same address.
- **Label freshness.** In `all.S`, each label is defined once. External labels are not defined there.
  This is the `LabelsFresh` premise of the theorems, checked on the real layout.
- **Reassembly.** `clang --target=x86_64-linux-gnu` assembles the `.S` text again at the original addresses.
  The result must be the ELF bytes. A difference passes only when LLVM decodes both byte strings to the same text, or when it is a normalized padding `nop`.
- **Order.** `all.S` has the same directives as the per-function files, in the same order.
- **Data.** Each data file names one ELF symbol. Its bytes are the ELF bytes at that place, and each pointer word is the address of its symbol plus its offset.

Three independent decoders read the same bytes: the Go disassembler, LLVM and the Kraken parser.
`check.py --selftest fv/kraken/link/out` changes copies of the test target inputs. Each mutated copy must fail, and a pure relabeling must pass.

The check does not read the Lean sources. It does not show that a theorem uses the included definitions.
A reader confirms that from the theorem statement.

## 3. What the result binds

`RESULT` has one line for each check, and a sha256 line for each input file.
The inputs are the ELF, the `.S` files, the data files and the Lean code file.
The last line is a bundle hash: the sha256 of `RESULT` up to the last PASS line.
One bundle hash thus binds the ELF to the exact text that Lean includes.

The tracked `RESULT` files also hash an axioms listing file that is no longer in the tree.
`check.py` hashes that file only if it exists. A new run can thus write a different bundle hash.

## 4. Requirements

- `data.py --check` on `link/out` needs Python only. The test target ELF is tracked.
- `conv.py` needs Python only, and a disassembly and symbol listing as input.
- `check.py` needs the ELF, `llvm-objdump` and `clang`.
- A Prysm link set needs the Prysm ELF and its symbol listing, which are not tracked (`../README.md` section 3).

```sh
python3 -B fv/kraken/link/data.py --check fv/kraken/link/out
python3 -B fv/kraken/link/check.py fv/kraken/link/out
python3 -B fv/kraken/link/check.py --selftest fv/kraken/link/out
```

## 5. Data file format

A data file is text. Each line has one directive. A line that starts with `#` is a comment.

| Directive | Meaning |
| --- | --- |
| `at <label> <offset>` | The first directive. The address of the item is the label plus the offset. The label is the short name that `conv.py` writes |
| `bytes <hex> ...` | Raw bytes, as two lowercase hexadecimal digits each, separated by spaces |
| `word <label> <offset>` | An 8-byte little-endian absolute address: the label plus the offset |

Offsets are decimal. Lines end with `\n`. All other characters are printable ASCII.
The reader in Lean and `check.py` both reject a tab, a `\r` or another control character.
An item with only an `at` line gives only an address. The error globals `ssz.Err*` are such items: the Go runtime sets their values at start.

## 6. The include interface

`data_include <id>` (`lean/Fk/Include.lean`) reads `link/out/data/<id>.data` and defines:

- `<id> : List UInt8`: the bytes of the item. A `word` line gives the 8 bytes of `(label "<label>" + <offset>)`. Then the definition depends on the `Host`.
- `<id>_addr : BitVec 64`: `(label "<label>" + <offset>).toBitVec`, without `+ 0` for offset 0.

The Prysm libraries use copies of this reader for their own data directories, for example `e2e_data_include` in `lean/E2e/Include.lean`.
`gen/e2e/check_include.py` compares the copies with the original text.

Rules for a new data file:

1. Take the addresses and lengths from the operands of the converted code. Read the bytes from the ELF. Do not write them by hand.
2. Write a pointer as `word <label> <offset>`. Use the nearest symbol at or below the value. If several symbols share the address, use the label that the code uses.
3. For an error global, extract only the address. A reject theorem takes the value as a premise.
4. Put the files of a new ELF in their own directory. Do not reuse the files of another ELF.
5. Declare the directory as a Lake `input_dir` of the library that includes it.

A format string is bound only by its length and by the absence of `%` where the contract needs that. Its content is not checked against the contract.
