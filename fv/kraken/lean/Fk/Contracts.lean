import Fk.Step

/-!
# Contracts of Go runtime functions (Kraken hypotheses)

A contract is a hypothesis about the code at a runtime label in the `Host`
program. It is quantified over every machine state, so the caller gets its
result at any call site (no havoc index, no result that picks a path;
CONTRACTS.md).

## `runtime.makeslice(et *_type, len, cap int) unsafe.Pointer`

`MakesliceC Heap ty esz S`:
- `Heap avail`: the runtime-owned heap with `avail` free bytes (an abstract
  predicate; the allocator's state lives in it);
- `ty`: the type descriptor address of the element type (rax), `esz` its size;
- the call is in range: `len ≤ cap = cnt`, `esz * cnt ≤ avail` (so Go's
  `panicmakeslicelen`/`panicmakeslicecap` and the out-of-memory throw are not
  taken; with a separated heap of `avail` bytes, `avail < 2^64`);
- `S` bytes of stack below the return slot are scratch for the callee;
- result: the callee returns to the return address with rsp + 8 (`Eventually`
  includes termination), the frame `F` unchanged, a zeroed block of
  `esz * cnt` bytes at rax carved from the heap, and `Heap (avail - esz * cnt)`.

The earlier form (no heap, every `cnt`, every frame) was contradictory: with
`cnt = 2^61` the block covers all addresses (review/ReviewKraken.lean,
`lu_accept_preconditions_false`). Here the block comes out of `Heap avail`,
so it is disjoint from `F` and from the return slot by `⋆`.
`Fk/Witness.lean` proves that an allocator satisfies this contract and that
the premises of `lu_accept_main` hold together (n = 0, 1, 16).

Not modeled: the write-barrier flag and other runtime globals the callee may
change (a garbage collection inside `makeslice`). They are in `F`, so the
contract says they do not change; CONTRACTS.md lists this as a premise.
-/

namespace Fk
variable [Host]

def MakesliceC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (cnt avail : Nat) (stk : List UInt8) (F : DataMem → Prop),
    st.regs.rax.toBitVec = ty → st.regs.rbx.toNat ≤ cnt → st.regs.rcx.toNat = cnt →
    esz * cnt ≤ avail → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ stk' : List UInt8, stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq ((List.replicate (esz * cnt) 0).At st'.data.regs.rax.toBitVec)
          ⋆ Heap (avail - esz * cnt) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.makeslice"⟩

/-- `runtime.memmove(to, from unsafe.Pointer, n uintptr)` (rax = to, rbx = from,
rcx = n): on disjoint source and destination chunks of n bytes, it returns with
rsp + 8 and the destination equal to the source; the source and the frame `F`
are unchanged. Overlapping ranges (allowed by Go) are outside this contract:
the callers' premises separate them (`⋆`). -/
def MemmoveC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (src dst stk : List UInt8) (F : DataMem → Prop),
    st.regs.rcx.toNat = src.length → dst.length = src.length → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
      ⋆ Eq (src.At st.regs.rbx.toBitVec) ⋆ Eq (dst.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
        ∃ stk' : List UInt8, stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (src.At st.regs.rbx.toBitVec) ⋆ Eq (src.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.memmove"⟩

/-- `runtime.convT64(v uint64) unsafe.Pointer` (rax = v; Go 1.26.3
runtime/iface.go): returns a non-nil pointer to a boxed copy of v (into the
read-only `staticuint64s` table for v < 256, otherwise an 8-byte allocation).
Premises: an 8-byte budget (`8 ≤ avail`), `S` scratch bytes, the 8-byte
argument spill slot above the return slot. Result: rsp + 8, r14 kept,
rax ≠ 0, the heap shrinks by at most 8 bytes (`avail' ≤ avail ≤ avail' + 8`),
the frame `F` unchanged. Not stated: the box's contents (the callers here
only pass the pointer to `fmt.errorf`, whose contract does not read it). -/
def ConvT64C (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk spill : List UInt8) (F : DataMem → Prop),
    8 ≤ avail → stk.length = S → spill.length = 8 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' spill' : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 8
          ∧ avail' ≤ avail ∧ avail ≤ avail' + 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.convT64"⟩

/-- The internal `fmt.errorf(format string, a ...any) error` of Go 1.26.3
(fmt/errors.go), not the public `fmt.Errorf`. Arguments: format = (rax, rbx),
a = (rcx, rdi, rsi).

`FmtErrorfNilC`: with no arguments (`len(a) = 0`) and no `%` (byte 0x25) in
the format, `errorf` returns nil without allocating (rax = 0). The public
`fmt.Errorf` then calls `errors.New`; the generated code inlines that part
(`runtime.newobject` + an `errors.errorString`), so the machine theorems
prove that path. Premises: the format bytes `fs` at rax (rbx = their length),
`S` scratch bytes, the 40-byte spill area of the five register arguments. -/
def FmtErrorfNilC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (fs stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = fs.length → st.regs.rdi = 0 → (0x25 : UInt8) ∉ fs → stk.length = S → spill.length = 40 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax = 0 ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 40 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "fmt.errorf"⟩

/-- `FmtErrorfC`: the internal `fmt.errorf` with at least one argument
(`1 ≤ len(a) = cap(a)`). Go then always formats and returns a non-nil error
(`errors.New`, `*wrapError` or `*wrapErrors`): rax ≠ 0. Premises: the format
bytes `fs` at rax, the argument array `args` (16 bytes per `any`) at rcx, a
heap, `S` scratch bytes, the 40-byte spill area. Result: rsp + 8, r14 kept,
`fs` and `args` unchanged, the heap shrinks (`avail' ≤ avail`), `F` unchanged.

Trusted, not narrowed further: fmt reads the values behind the interface
words (in `F`) and calls `Error()` on `%w` arguments; the contract assumes
that this terminates and writes nothing in `F` (CONTRACTS.md). -/
def FmtErrorfC (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (fs args stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rbx.toNat = fs.length → 1 ≤ st.regs.rdi.toNat → st.regs.rsi = st.regs.rdi →
    args.length = 16 * st.regs.rdi.toNat → stk.length = S → spill.length = 40 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ Eq (args.At st.regs.rcx.toBitVec) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' spill' : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 40 ∧ avail' ≤ avail ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ Eq (args.At st.regs.rcx.toBitVec) ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "fmt.errorf"⟩

/-- Go's `maxAlloc` on linux/amd64: `1 << heapAddrBits`, heapAddrBits = 48
(runtime/malloc.go). `growslice` and `makeslice` panic above it. -/
def maxAlloc : Nat := 2 ^ 48

/-- The growth loop of Go 1.26.3 `runtime.nextslicecap` (slice.go):
`newcap += (newcap + 3*256) >> 2` until `newcap ≥ newLen`. The fuel argument
only makes the recursion structural; `growLoop_ge` shows that fuel `newLen`
always reaches the exit test, so the result is Go's. -/
def growLoop : Nat → Nat → Nat → Nat
  | 0, c, _ => c
  | f + 1, c, n => if n ≤ c + (c + 768) / 4 then c + (c + 768) / 4 else growLoop f (c + (c + 768) / 4) n

/-- Go 1.26.3 `runtime.nextslicecap(newLen, oldCap)` for sizes below 2^62 (no
`int` overflow, so the `newcap <= 0` fallback is not taken). -/
def nextSliceCap (newLen oldCap : Nat) : Nat :=
  if 2 * oldCap < newLen then newLen else if oldCap < 256 then 2 * oldCap else growLoop newLen oldCap newLen

theorem growLoop_ge (f c n : Nat) (h : n ≤ c + 192 * f) : n ≤ growLoop f c n := by
  induction f generalizing c with
  | zero => simp [growLoop] at h ⊢; omega
  | succ f ih =>
    simp only [growLoop]
    split
    · assumption
    · exact ih _ (by omega)

theorem growLoop_le (f c n : Nat) (h : c < n) : growLoop f c n ≤ 2 * n + 192 := by
  induction f generalizing c with
  | zero => simp [growLoop]; omega
  | succ f ih =>
    simp only [growLoop]
    split
    · omega
    · exact ih _ (by omega)

theorem nextSliceCap_ge (n o : Nat) : n ≤ nextSliceCap n o := by
  unfold nextSliceCap
  split
  · exact Nat.le_refl _
  · split
    · omega
    · exact growLoop_ge _ _ _ (by omega)

theorem nextSliceCap_le (n o : Nat) (h : o < n) : nextSliceCap n o ≤ 2 * n + 192 := by
  unfold nextSliceCap
  split
  · omega
  · split
    · omega
    · exact growLoop_le _ _ _ h

theorem nextSliceCap_zero (n : Nat) (h : 0 < n) : nextSliceCap n 0 = n := by
  simp [nextSliceCap, h]

/-- `runtime.growslice(oldPtr, newLen, oldCap, num, et) slice` (rax, rbx, rcx,
rdi, rsi; result rax = new ptr, rbx = newLen, rcx = newCap), Go 1.26.3
(runtime/slice.go), for an element type of `esz` bytes at `ty`.

Premises (the in-range call; Go's compiler emits the call only when
`newLen > oldCap`):
- `0 < esz` (Go returns `zerobase` with cap = newLen for `esz = 0`);
- `num ≤ newLen`, `oldLen = newLen − num ≤ oldCap < newLen`;
- growth policy and budget: with `nc = nextSliceCap newLen oldCap`, the heap
  has `2·esz·nc + 8192 ≤ avail` free bytes, and this is at most `maxAlloc`
  (Go's `roundupsize(n) ≤ 2n + 8192` for its size classes and page rounding;
  REPORT-1b-fix X1). So `newLen < 2^48`: the signed range and the
  `growslice: len out of range` panics are excluded;
- `old`: the `esz·oldLen` old bytes at oldPtr; `stk`: `S` scratch bytes below
  the return slot; `spill`: the 40-byte argument spill area above it (Go
  ABIInternal: the callee owns the spill slots of its five register arguments);
- `Heap avail`: the runtime-owned heap; `F`: the frame.

Result: return to `ret` with rsp + 8, rbp and r14 (Go's g) preserved,
rbx = newLen, `nc ≤ newCap` and `esz·newCap ≤ 2·esz·nc + 8192`; a block of
`esz·newCap` bytes at the new pointer that starts with `old` (the rest is
unspecified), carved from the heap (`avail' + esz·newCap ≤ avail`); the old
block and `F` unchanged; the scratch and spill bytes changed.

The 1b form had no range and no budget; with `newLen = 2^63` its result was
contradictory (review/Review1b.lean). `Fk/RtCopy.lean` proves that a bump
allocator satisfies this form (`rt_growslice`). -/
def GrowsliceC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (old stk spill : List UInt8) (avail : Nat) (F : DataMem → Prop),
    0 < esz → st.regs.rsi.toBitVec = ty → st.regs.rdi.toNat ≤ st.regs.rbx.toNat →
    st.regs.rbx.toNat - st.regs.rdi.toNat ≤ st.regs.rcx.toNat → st.regs.rcx.toNat < st.regs.rbx.toNat →
    2 * (esz * nextSliceCap st.regs.rbx.toNat st.regs.rcx.toNat) + 8192 ≤ avail → avail ≤ maxAlloc →
    old.length = esz * (st.regs.rbx.toNat - st.regs.rdi.toNat) → stk.length = S → spill.length = 40 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (old.At st.regs.rax.toBitVec) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.r14 = st.regs.r14 ∧ st'.data.regs.rbx = st.regs.rbx
        ∧ nextSliceCap st.regs.rbx.toNat st.regs.rcx.toNat ≤ st'.data.regs.rcx.toNat
        ∧ esz * st'.data.regs.rcx.toNat ≤ 2 * (esz * nextSliceCap st.regs.rbx.toNat st.regs.rcx.toNat) + 8192 ∧
        ∃ (stk' spill' tail : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 40
          ∧ old.length + tail.length = esz * st'.data.regs.rcx.toNat ∧ avail' + esz * st'.data.regs.rcx.toNat ≤ avail ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (old.At st.regs.rax.toBitVec)
          ⋆ Eq ((old ++ tail).At st'.data.regs.rax.toBitVec) ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.growslice"⟩

/-- Consequences of the result bounds: `newLen ≤ newCap ≤ 2^48`. -/
theorem growslice_cap_bounds {esz n o c : Nat} (he : 0 < esz) (hb : 2 * (esz * nextSliceCap n o) + 8192 ≤ maxAlloc)
    (h1 : nextSliceCap n o ≤ c) (h2 : esz * c ≤ 2 * (esz * nextSliceCap n o) + 8192) :
    n ≤ c ∧ c ≤ 2 ^ 48 := by
  have := nextSliceCap_ge n o
  refine ⟨by omega, ?_⟩
  have : c ≤ esz * c := Nat.le_mul_of_pos_left c he
  unfold maxAlloc at hb; omega

end Fk
