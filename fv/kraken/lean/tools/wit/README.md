# Witness generators (1b-fix X4)

`wgen.py` writes a witness file `Fk/Wit*.lean`: a host (data labels, target,
callees, runtime models), a memory block from 0x10000, `s_mem` (the premise's
memory from the block) and `*_runs` (the main theorem applied to the block).
`gen` is for theorems with a heap (bump allocator), `gen2` for heap-free ones.

Run from `fv/kraken/lean`:

    python3 tools/wit/wne0.py tools/wit      # Fk/WitNe0.lean (also wne1, wne16)
    python3 tools/wit/wadm.py tools/wit 3     # Fk/WitAdM.lean, 3-byte prefix

The other witness files (`WitFv`, `WitCp`, `WitBv`, `WitAd`, `WitCpM`) were
generated with the same functions from configurations written inline; the
generated files are the record.

## Go value check (re-proof fix X4)

`goval.py` reads every `Fk/Wit*.lean`, rebuilds the block layout from
0x10000 and the start registers, and checks the Go values of the call: the
argument slice, the receiver's slice fields and pointer fields. A slice
header (p, len, cap) needs len ≤ cap < 2^63 and, if cap > 0, its data
p .. p + cap·esz in the block. The last run is in `goval-result.txt`.

    python3 tools/wit/goval.py          # exit 1 on a violation

A main theorem may allow more machine states than Go values (it is stronger
then). The witness must still be a Go value: "premise met" and "Go value"
are two columns of the completion table.

## Re-proof fix X8 generators

    python3 tools/wit/wlca.py tools/wit 1    # Fk/WitLcA1.lean (also 4): lc_accept_main
    python3 tools/wit/wlcm.py tools/wit 0    # Fk/WitLcM0.lean (also 1, 4): lc_marshal_main
    python3 tools/wit/wlcs.py tools/wit 0    # Fk/WitLcS0.lean (also 1, 4): lc_size_main
    python3 tools/wit/wnes.py tools/wit 0    # Fk/WitNeS0.lean (also 1, 16): ne_size_main
    python3 tools/wit/wlug.py tools/wit      # Fk/WitLuG.lean: lum_grow_site

`wgen.gen` takes `heap_end=True` to put the heap after the other chunks (when
a label offset such as `go_string._+526` would fall into the heap).

## Go layout and the fix 2 checks (re-proof fix 2, X3)

`goval.py` reads the Go object layout from `layout.json`, not from a table
by hand. `layout.go` writes it: the constant values of `unsafe.Sizeof`,
`unsafe.Alignof` and `unsafe.Offsetof` for every struct of
`fv/kraken/target` and `fv/kraken/target/prysm`, type-checked with the gc
amd64 sizes (GOOS=linux, GOARCH=amd64; no amd64 binary runs on the host).

    cd ../../../.. && go run fv/kraken/lean/tools/wit/layout.go > fv/kraken/lean/tools/wit/layout.json

The checks: slice headers, object size and alignment (Scalars is 24 bytes in
Go, 16 in SSZ), rsp 8-aligned, bool bytes 0 or 1, the errorString itab type
word (itab+8) where the premise places it, and overlap: the Go objects are
pairwise disjoint and every `s_mem` chunk is inside one Go object or outside
all of them. A value the script cannot read is "not checked" (counted).

`wgen.gen` puts a 4-byte gap after the bump pointer: the heap and the first
chunk start at `wgen.CH0` = 0x10010 (8-aligned). `wgen.aligned` inserts gap
chunks before the named chunks. `WitCp`, `WitFv`, `WitAd` have no generator;
they were shifted once by the same 4-byte gap (the files are the record).
