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
