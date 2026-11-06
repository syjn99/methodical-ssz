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
- the call is in range (Go 1.26.3 runtime/slice.go `makeslice`): `len ≤ cap =
  cnt`, `cnt < 2^63` (Go `int`, so `len < 0` and `cap < 0` are excluded),
  `esz * cnt ≤ maxAlloc` (`panicmakeslicecap` excluded), `esz * cnt ≤ avail`
  (the out-of-memory throw excluded);
- `S` bytes of stack below the return slot are scratch for the callee, and the
  24-byte spill area of its three register arguments above the return slot
  (Go ABIInternal) is the callee's too;
- result: the callee returns to the return address with rsp + 8 (`Eventually`
  includes termination), r14 (Go's g) and rbp kept, the frame `F` unchanged,
  a zeroed block of `esz * cnt` bytes at rax carved from the heap, and
  `Heap (avail - esz * cnt)`.

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

/-- Go's `maxAlloc` on linux/amd64: `1 << heapAddrBits`, heapAddrBits = 48
(runtime/malloc.go). `growslice` and `makeslice` panic above it. -/
def maxAlloc : Nat := 2 ^ 48

variable [Host]

def MakesliceC (Heap : Nat → DataMem → Prop) (ty : BitVec 64) (esz S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (cnt avail : Nat) (stk spill : List UInt8) (F : DataMem → Prop),
    st.regs.rax.toBitVec = ty → st.regs.rbx.toNat ≤ cnt → st.regs.rcx.toNat = cnt →
    esz * cnt ≤ avail → esz * cnt ≤ maxAlloc → cnt < 2 ^ 63 → stk.length = S → spill.length = 24 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rbp = st.regs.rbp ∧
        ∃ stk' spill' : List UInt8, stk'.length = S ∧ spill'.length = 24 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((List.replicate (esz * cnt) 0).At st'.data.regs.rax.toBitVec)
          ⋆ Heap (avail - esz * cnt) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.makeslice"⟩

/-- `runtime.memmove(to, from unsafe.Pointer, n uintptr)` (rax = to, rbx = from,
rcx = n): on disjoint source and destination chunks of n bytes, it returns with
rsp + 8, r14 (Go's g) and rbp kept, and the destination equal to the source;
the source and the frame `F` are unchanged. Go's memmove is an assembly
function with a zero-byte frame (`$0-24`, memmove_amd64.s): it has no spill
slots and does not write the stack (S = 0 suffices; callers may pass more). Overlapping ranges (allowed by Go) are outside this contract:
the callers' premises separate them (`⋆`). -/
def MemmoveC (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (src dst stk : List UInt8) (F : DataMem → Prop),
    st.regs.rcx.toNat = src.length → dst.length = src.length → stk.length = S →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
      ⋆ Eq (src.At st.regs.rbx.toBitVec) ⋆ Eq (dst.At st.regs.rax.toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8
        ∧ st'.data.regs.r14 = st.regs.r14 ∧ st'.data.regs.rbp = st.regs.rbp ∧
        ∃ stk' : List UInt8, stk'.length = S ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S))
          ⋆ Eq (src.At st.regs.rbx.toBitVec) ⋆ Eq (src.At st.regs.rax.toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label "runtime.memmove"⟩

/-- The 8-byte entry `v` of Go's read-only `runtime.staticuint64s` table
(`staticuint64s[v] = v`), for v < 256; nothing otherwise (fix 2 X4). The
table bytes in the ELF are checked by `link/check.py` (h). -/
def StaticBox (v : BitVec 64) : DataMem → Prop :=
  if v.toNat < 256 then Eq ((Int.toBytes 8 v.toInt).At ((label "runtime.staticuint64s").toBitVec + 8 * v))
  else Eq (([] : List UInt8).At 0)

/-- Where `convT64`'s box `bx` of the value `v` is (fix 2 X4): in the static
table (`hb = []`, v < 256, bx = staticuint64s + 8v; the bytes are in
`StaticBox v`) or in 8 heap bytes `hb = v` at bx. -/
def BoxIn (bx v : BitVec 64) (hb : List UInt8) : Prop :=
  (hb = [] ∧ v.toNat < 256 ∧ bx = (label "runtime.staticuint64s").toBitVec + 8 * v) ∨ hb = Int.toBytes 8 v.toInt

/-- `runtime.convT64(v uint64) unsafe.Pointer` (rax = v; Go 1.26.3
runtime/iface.go): returns a pointer to a box of v (fix 2 X4: the box is
stated). For v < 256 Go returns `&staticuint64s[v]` (read-only, no
allocation); otherwise an 8-byte allocation holding v. Premises: an 8-byte
budget, `S` scratch bytes, the 8-byte argument spill slot, the static entry
`StaticBox v` (read-only, kept). Result: rsp + 8, r14 kept, rax = bx with
`BoxIn bx v hb`, the heap bytes `hb` at bx are new
(`avail' + hb.length ≤ avail ≤ avail' + 8`), the frame `F` unchanged. -/
def ConvT64C (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (stk spill : List UInt8) (F : DataMem → Prop),
    8 ≤ avail → stk.length = S → spill.length = 8 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ StaticBox st.regs.rax.toBitVec ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (stk' spill' hb : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 8
          ∧ BoxIn st'.data.regs.rax.toBitVec st.regs.rax.toBitVec hb
          ∧ avail' + hb.length ≤ avail ∧ avail ≤ avail' + 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ StaticBox st.regs.rax.toBitVec ⋆ Eq (hb.At st'.data.regs.rax.toBitVec) ⋆ Heap avail' ⋆ F) st'.data.dmem)
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

/-- No bytes: the empty heap (the rodata case of a message, fix 2 X5). -/
theorem errNil_At_emp (a : BitVec 64) : Eq (([] : List UInt8).At a) = Std.ExtHashMap.emp := by
  funext m; apply propext; simp only [List.At, List.mapIdx_nil, Std.ExtHashMap.ofList_nil, Std.ExtHashMap.emp]
  exact ⟨Eq.symm, Eq.symm⟩

/-- The 16-byte `*errors.errorString` object at `e`: string data pointer `sp`
and the length of `msg` (fix 2 X5: the object alone; the message bytes are a
separate resource, in rodata or on the heap). -/
def ErrObj (e sp : BitVec 64) (msg : List UInt8) : DataMem → Prop :=
  Eq ((Int.toBytes 8 sp.toInt ++ Int.toBytes 8 (BitVec.ofNat 64 msg.length).toInt).At e)

/-- A Go `*errors.errorString` at `e` with its message bytes at `sp`
(re-proof fix X5). -/
def ErrStr (e sp : BitVec 64) (msg : List UInt8) : DataMem → Prop :=
  ErrObj e sp msg ⋆ Eq (msg.At sp)

/-- `FmtErrorfWC Heap fs RO MsgIn S` (fix 2 X4): the internal `fmt.errorf`
for one fixed format `fs` with one `%w` verb (the generated `"J: %w"`,
`"B: %w"`; the theorems name the constant, `link/check.py` (g) compares it
with the ELF and the Go source) and one argument: an `*errors.errorString`
error, type word `ity` (the word at `itab + 8` of the errorString itab, read
there by the code), data word `e`. The object `ErrObj e sp msg` and the
message are in the footprint: `MsgIn sp msg hm` says where the message
bytes are, in `hm` at `sp` or in the read-only resource `RO` (rodata strings
of the caller; fixed by the caller with `MsgIn`). Allocation budget,
computed from the format and the argument: `fs.length + msg.length + 8192 ≤
avail` (the formatted string `len(fs) - 2 + len(msg)`, the 32-byte
`*fmt.wrapError`, the printer). Result: rsp + 8, r14 kept, rax ≠ 0, every
read resource unchanged, the heap shrinks, `F` unchanged.
Trusted: Go's allocation stays within the budget; no GC during the call. -/
def FmtErrorfWC (Heap : Nat → DataMem → Prop) (fs : List UInt8) (RO : DataMem → Prop)
    (MsgIn : BitVec 64 → List UInt8 → List UInt8 → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (ity msg hm stk spill : List UInt8) (e sp : BitVec 64)
    (F : DataMem → Prop),
    st.regs.rbx.toNat = fs.length → st.regs.rdi = 1 → st.regs.rsi = 1 →
    ity.length = 8 → MsgIn sp msg hm → stk.length = S → spill.length = 40 →
    fs.length + msg.length + 8192 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ Eq ((ity ++ Int.toBytes 8 e.toInt).At st.regs.rcx.toBitVec)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
      ⋆ ErrObj e sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' spill' : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 40 ∧ avail' ≤ avail ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fs.At st.regs.rax.toBitVec) ⋆ Eq ((ity ++ Int.toBytes 8 e.toInt).At st.regs.rcx.toBitVec)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8))
          ⋆ ErrObj e sp msg ⋆ Eq (hm.At sp) ⋆ RO ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "fmt.errorf"⟩

/-- `FmtErrorfDWC Heap fs tw S` (fix 2 X4): the internal `fmt.errorf` for one
fixed format `fs` with `%d` then `%w` (the two ListU64 formats) and two
arguments: an `int` box (type word `tw`, the theorems fix it to the ELF's
`type:int` descriptor, checked by `link/check.py` (h); data word `bx`, the
`convT64` box of `v`, its bytes in `StaticBox v` or `hb`: `BoxIn bx v hb`) and
an `*errors.errorString` error (type word `ity` at `itab + 8`, data word
`e`, `ErrStr e sp msg`). Budget from the format and the arguments:
`fs.length + 20 + msg.length + 8192 ≤ avail` (at most 20 digits). Result as
`FmtErrorfWC`. -/
def FmtErrorfDWC (Heap : Nat → DataMem → Prop) (fs : List UInt8) (tw : BitVec 64) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (ity msg hb stk spill : List UInt8) (bx v e sp : BitVec 64)
    (F : DataMem → Prop),
    st.regs.rbx.toNat = fs.length → st.regs.rdi = 2 → st.regs.rsi = 2 →
    ity.length = 8 → BoxIn bx v hb → stk.length = S → spill.length = 40 →
    fs.length + 20 + msg.length + 8192 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fs.At st.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e.toInt).At st.regs.rcx.toBitVec)
      ⋆ StaticBox v ⋆ Eq (hb.At bx)
      ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8)) ⋆ ErrStr e sp msg
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' spill' : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 40 ∧ avail' ≤ avail ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fs.At st.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx.toInt ++ ity ++ Int.toBytes 8 e.toInt).At st.regs.rcx.toBitVec)
          ⋆ StaticBox v ⋆ Eq (hb.At bx)
          ⋆ Eq (ity.At ((label "go_itab._errors.errorString_error").toBitVec + 8)) ⋆ ErrStr e sp msg
          ⋆ Heap avail' ⋆ F) st'.data.dmem)
      ⟨st, label "fmt.errorf"⟩

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
