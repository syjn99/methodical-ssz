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
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
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

/-- `runtime.convT64(v uint64) unsafe.Pointer`: returns to the return address
with rsp + 8; the heap may shrink (it allocates for values ≥ 256), the frame
`F` is unchanged. The result is not used by the callers proved here beyond
being passed on. -/
def ConvT64C (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk : List UInt8) (F : DataMem → Prop),
    stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧
        ∃ (stk' : List UInt8) (avail' : Nat), stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.convT64"⟩

/-- `fmt.Errorf(format string, a ...any) error` (`fmt.errorf` in the binary):
returns to the return address with rsp + 8 and a non-nil error interface
(rax ≠ 0, the itab word); the heap may shrink; the frame `F` (which holds the
argument slice the caller built) is unchanged. Not modeled: which error it
wraps (`%w`); CONTRACTS.md. -/
def FmtErrorfC (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk : List UInt8) (F : DataMem → Prop),
    stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' : List UInt8) (avail' : Nat), stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "fmt.errorf"⟩

/-- `runtime.growslice(oldPtr, newLen, oldCap, num, et) slice` (rax, rbx, rcx,
rdi, rsi; result rax = new ptr, rbx = newLen, rcx = newCap): for an element
type of `esz` bytes at `ty`, it returns to the return address with rsp + 8, a
new capacity `newCap ≥ newLen` (below 2^63), and a block of `esz * newCap`
bytes at the new pointer whose first bytes are the old elements `old`
(rbp is preserved: Go's frame-pointer convention)
(`esz * (newLen - num)` bytes); the old block, the frame `F` stay; the heap
may shrink. The tail's contents are not specified. -/
def GrowsliceC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (old stk : List UInt8) (avail : Nat) (F : DataMem → Prop),
    st.regs.rsi.toBitVec = ty → st.regs.rdi.toNat ≤ st.regs.rbx.toNat →
    old.length = esz * (st.regs.rbx.toNat - st.regs.rdi.toNat) → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (old.At st.regs.rax.toBitVec)
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp
        ∧ st'.data.regs.rbx = st.regs.rbx ∧ st.regs.rbx.toNat ≤ st'.data.regs.rcx.toNat ∧ st'.data.regs.rcx.toNat < 2 ^ 63 ∧
        ∃ (stk' tail : List UInt8) (avail' : Nat), stk'.length = S
          ∧ old.length + tail.length = esz * st'.data.regs.rcx.toNat ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (old.At st.regs.rax.toBitVec)
          ⋆ Eq ((old ++ tail).At st'.data.regs.rax.toBitVec) ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.growslice"⟩

end Fk
