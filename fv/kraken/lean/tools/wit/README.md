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
