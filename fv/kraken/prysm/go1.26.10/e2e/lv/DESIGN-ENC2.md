# DESIGN-ENC2: any-site grow path (encoder for all capacities) design

This file is committed before the any-site grow path proof. It is a plan.
The statements are in `lean/E2eEnc/StmtEncG.lean`.

## Any-site grow path

- dst is `(dp, len, cap)`. The old block is `pre ‖ spare`, and `len + |spare| = cap`.
- There are n + 2 append sites: site 1 (BlockRoot), site 2 (WriteOffset), the n sites of the loop.
- Any site can call growslice. The contract is one `GrowsliceC Heap e2eU8Type_addr 1 S`.
- One call needs `2·nextSliceCap + 8192` bytes. The written amount is also at most that.
- newLen ≤ L = len + 36 + 8n, and `nextSliceCap ≤ 2·L + 192`. Thus K = 4·L + 8576 per site is sufficient.
- Heap premise: `(n + 2)·K ≤ avail`. Invariant: if r sites remain, the remaining heap ≥ r·K.

## Postcondition

- Result block: `pre ‖ root ‖ dcOff ‖ cb ‖ rest`, `len + 36 + 8n + |rest| = result cap`.
- After each grow, the old block (the copied front part and the unwritten spare) remains. The existential predicate `G` collects them.
- If there is no grow, `G` is empty and the result block is the old block.
- The slots that only the grow path uses (x + 24, x − 16, x − 48, x − 72, spill 40) are in the premises. They are existential variables in the postcondition.

## Proof form

- Head (0–28): if site 1 fits, the head of the fast path, otherwise the head of the first-site grow path. Both branches reach a state of the same form at L_7c (29).
- Tail (29–60): memmove, site 2 (fits or grows 45–49), movl, n, Columns pointer.
- Loop invariant (82): block = `Pfx ‖ cb.take (8i) ‖ tail`, `|tail| = cp − (L₀ + 8i)`, garbage `G`, heap ≥ (n − i)·K.
  x − 24 (pc) and x − 40 (n) are in the invariant. The grow branch (90–99) reads those slots again.
- The one-iteration theorem has two branches: fits (89 `jae` taken) or grows (94 growslice, 99 `jmp L_132`).
