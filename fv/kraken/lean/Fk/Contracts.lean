import Fk.Step
import Fk.Data

/-!
# Contracts of Go runtime functions (Kraken hypotheses)

A contract is a hypothesis about the code at a runtime label in the `Host`
program.
-/

namespace Fk

/-- Go's `maxAlloc` on linux/amd64: `1 << heapAddrBits`, heapAddrBits = 48
(runtime/malloc.go). `growslice` and `makeslice` panic above it. -/
def maxAlloc : Nat := 2 ^ 48

variable [Host]

/-- `runtime.makeslice(et *_type, len, cap int)` (Go 1.26.3 runtime/slice.go).
`Heap avail` is the runtime heap with `avail` free bytes; `ty` (rax) is the
element type descriptor, `esz` its size. In range: `len ≤ cap = cnt < 2^63`,
`esz * cnt ≤ maxAlloc`, `esz * cnt ≤ avail`. `S` stack bytes below the return
slot and the 24-byte spill area above it are the callee's. Result: return with
rsp + 8, r14 and rbp kept, `F` unchanged, a zeroed `esz * cnt`-byte block at rax
carved from the heap, and `Heap (avail - esz * cnt)`. -/
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

/-- The 8-byte entry `v` of Go's read-only `runtime.staticuint64s` table, for
v < 256; nothing otherwise. The bytes are the included ELF table
(`Fk.Data.staticuint64s`); `staticBox_of_lt` shows that the entry holds v. -/
def StaticBox (v : BitVec 64) : DataMem → Prop :=
  if v.toNat < 256 then Eq (((Data.staticuint64s.drop (8 * v.toNat)).take 8).At (Data.staticuint64s_addr + 8 * v))
  else Eq (([] : List UInt8).At 0)

omit [Host] in
/-- The k-byte chunk i of a concatenation of k-byte chunks. -/
theorem flatMap_range_chunk {α : Type} (f : Nat → List α) (k : Nat) (hf : ∀ j, (f j).length = k) :
    ∀ n i, i < n → (((List.range n).flatMap f).drop (k * i)).take k = f i := by
  have hl : ∀ m, ((List.range m).flatMap f).length = k * m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hf, Nat.mul_succ]
  intro n
  induction n with
  | zero => intro i h; omega
  | succ n ih =>
    intro i hi
    have hlen := hl n
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge i n with h | h
    · rw [List.drop_append_of_le_length (by rw [hlen]; exact Nat.mul_le_mul_left k (Nat.le_of_lt h)),
        List.take_append_of_le_length (by rw [List.length_drop, hlen, ← Nat.mul_sub]; exact Nat.le_mul_of_pos_right k (by omega)), ih i h]
    · have : i = n := by omega
      subst this
      rw [List.drop_append_of_le_length (by rw [hlen]; omega), List.drop_eq_nil_of_le (by rw [hlen]; omega), List.nil_append,
        List.take_of_length_le (by rw [hf]; omega)]

omit [Host] in
/-- The table entry v (v < 256) is the 8-byte value v. -/
theorem staticuint64s_entry (v : BitVec 64) (h : v.toNat < 256) :
    (Data.staticuint64s.drop (8 * v.toNat)).take 8 = Int.toBytes 8 v.toInt := by
  rw [Data.staticuint64s_table, flatMap_range_chunk _ 8 (fun _ => Int.toBytes_length _ _) 256 _ h]
  congr 1
  rw [BitVec.toInt_eq_toNat_of_lt (by omega)]

theorem staticBox_of_lt {v : BitVec 64} (h : v.toNat < 256) :
    StaticBox v = Eq ((Int.toBytes 8 v.toInt).At (Data.staticuint64s_addr + 8 * v)) := by
  rw [StaticBox, if_pos h, staticuint64s_entry v h]

/-- Where `convT64`'s box `bx` of the value `v` is: in the static table (`hb = []`,
v < 256, bx = staticuint64s + 8v; the bytes are in `StaticBox v`) or in 8 heap
bytes `hb = v` at bx. -/
def BoxIn (bx v : BitVec 64) (hb : List UInt8) : Prop :=
  (hb = [] ∧ v.toNat < 256 ∧ bx = Data.staticuint64s_addr + 8 * v) ∨ hb = Int.toBytes 8 v.toInt

/-- `runtime.convT64(v uint64) unsafe.Pointer` (rax = v; Go 1.26.3
runtime/iface.go): returns a pointer to a box of v. For v < 256 Go returns
`&staticuint64s[v]` (read-only, no allocation); otherwise an 8-byte allocation
holding v. Premises: an 8-byte budget, `S` scratch bytes, the 8-byte argument
spill slot, the static entry `StaticBox v` (read-only, kept). Result: rsp + 8,
r14 kept, rax = bx with `BoxIn bx v hb`, the heap bytes `hb` at bx are new
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

/-- No bytes: the empty heap. -/
theorem errNil_At_emp (a : BitVec 64) : Eq (([] : List UInt8).At a) = Std.ExtHashMap.emp := by
  funext m; apply propext; simp only [List.At, List.mapIdx_nil, Std.ExtHashMap.ofList_nil, Std.ExtHashMap.emp]
  exact ⟨Eq.symm, Eq.symm⟩

/-- The 16-byte `*errors.errorString` object at `e`: string data pointer `sp` and
the length of `msg`. -/
def ErrObj (e sp : BitVec 64) (msg : List UInt8) : DataMem → Prop :=
  Eq ((Int.toBytes 8 sp.toInt ++ Int.toBytes 8 (BitVec.ofNat 64 msg.length).toInt).At e)

/-- A Go `*errors.errorString` at `e` with its message bytes at `sp`. -/
def ErrStr (e sp : BitVec 64) (msg : List UInt8) : DataMem → Prop :=
  ErrObj e sp msg ⋆ Eq (msg.At sp)

/-- `FmtErrorfWC Heap fs RO MsgIn S`: the internal `fmt.errorf` for one fixed format
`fs` with one `%w` verb (the generated `"J: %w"`, `"B: %w"`; the theorems name
the included ELF bytes `Fk.Data.bvFmtJ`, `Fk.Data.blFmtB`)
and one argument: an `*errors.errorString` error, type word `ity` (the word at
`itab + 8` of the errorString itab, read there by the code), data word `e`. The
object `ErrObj e sp msg` and the message are in the footprint: `MsgIn sp msg hm`
says where the message bytes are, in `hm` at `sp` or in the read-only resource
`RO` (rodata strings of the caller; fixed by the caller with `MsgIn`).
Allocation budget, computed from the format and the argument: `fs.length +
msg.length + 8192 ≤ avail` (the formatted string `len(fs) - 2 + len(msg)`, the
32-byte `*fmt.wrapError`, the printer). Result: rsp + 8, r14 kept, rax ≠ 0,
every read resource unchanged, the heap shrinks, `F` unchanged. Trusted: Go's
allocation stays within the budget; no GC during the call. -/
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

/-- `FmtErrorfDWC Heap fs tw S`: the internal `fmt.errorf` for one fixed format `fs`
with `%d` then `%w` (the two ListU64 formats) and two arguments: an `int` box
(type word `tw`, the theorems fix it to `Fk.Data.intType_addr`, the ELF's
`type:int` descriptor, `Fk.Data.intType_size_kind`); data word `bx`, the `convT64` box of `v`, its bytes in
`StaticBox v` or `hb`: `BoxIn bx v hb`) and an `*errors.errorString` error (type
word `ity` at `itab + 8`, data word `e`, `ErrStr e sp msg`). Budget from the
format and the arguments: `fs.length + 20 + msg.length + 8192 ≤ avail` (at most
20 digits). Result as `FmtErrorfWC`. -/
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

/-- `FmtErrorfDDC Heap fs tw S`: the internal `fmt.errorf` for one fixed
format `fs` with two `%d` verbs (the ListC offset-order format `Fk.Data.lcFmtOrder`)
and two arguments: two `uint64` boxes (type word `tw` each, the theorems fix it to
`Fk.Data.uint64Type_addr`; data words `bx1`, `bx2`, the `convT64` boxes of `v1`,
`v2`, `BoxIn`). Budget from the format and the arguments: `fs.length + 40 + 8192
≤ avail` (at most 20 digits each). Result as `FmtErrorfWC`: rsp + 8, r14 kept,
rax ≠ 0, every read resource unchanged, the heap shrinks, `F` unchanged. -/
def FmtErrorfDDC (Heap : Nat → DataMem → Prop) (fs : List UInt8) (tw : BitVec 64) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (avail : Nat) (hb1 hb2 stk spill : List UInt8) (bx1 v1 bx2 v2 : BitVec 64)
    (F : DataMem → Prop),
    st.regs.rbx.toNat = fs.length → st.regs.rdi = 2 → st.regs.rsi = 2 →
    BoxIn bx1 v1 hb1 → BoxIn bx2 v2 hb2 → stk.length = S → spill.length = 40 →
    fs.length + 40 + 8192 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (stk.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (fs.At st.regs.rax.toBitVec)
      ⋆ Eq ((Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx1.toInt ++ Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx2.toInt).At
          st.regs.rcx.toBitVec)
      ⋆ StaticBox v1 ⋆ Eq (hb1.At bx1) ⋆ StaticBox v2 ⋆ Eq (hb2.At bx2)
      ⋆ Heap avail ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.r14 = st.regs.r14
        ∧ st'.data.regs.rax ≠ 0 ∧
        ∃ (stk' spill' : List UInt8) (avail' : Nat), stk'.length = S ∧ spill'.length = 40 ∧ avail' ≤ avail ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq (stk'.At (st.regs.rsp.toBitVec - BitVec.ofNat 64 S)) ⋆ Eq (spill'.At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq (fs.At st.regs.rax.toBitVec)
          ⋆ Eq ((Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx1.toInt ++ Int.toBytes 8 tw.toInt ++ Int.toBytes 8 bx2.toInt).At
              st.regs.rcx.toBitVec)
          ⋆ StaticBox v1 ⋆ Eq (hb1.At bx1) ⋆ StaticBox v2 ⋆ Eq (hb2.At bx2)
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

/--  `runtime.growslice(oldPtr, newLen, oldCap, num, et) slice` (rax, rbx, rcx,
rdi, rsi; result rax = new ptr, rbx = newLen, rcx = newCap), Go 1.26.3
(runtime/slice.go), for an element type of `esz` bytes at `ty`.

Premises (the in-range call; Go's compiler emits the call only when
`newLen > oldCap`):
- `0 < esz` (Go returns `zerobase` with cap = newLen for `esz = 0`);
- `num ≤ newLen`, `oldLen = newLen − num ≤ oldCap < newLen`;
- growth policy and budget: with `nc = nextSliceCap newLen oldCap`, the heap has
  `2·esz·nc + 8192 ≤ avail` free bytes, and this is at most `maxAlloc` (Go's
  `roundupsize(n) ≤ 2n + 8192` for its size classes and page rounding; So
  `newLen < 2^48`: the signed range and the `growslice: len out of range` panics
  are excluded;
- `old`: the `esz·oldLen` old bytes at oldPtr; `stk`: `S` scratch bytes below
  the return slot; `spill`: the 40-byte argument spill area above it (Go
  ABIInternal: the callee owns the spill slots of its five register arguments);
- `Heap avail`: the runtime-owned heap; `F`: the frame.

Result: return to `ret` with rsp + 8, rbp and r14 (Go's g) preserved,
rbx = newLen, `nc ≤ newCap` and `esz·newCap ≤ 2·esz·nc + 8192`; a block of
`esz·newCap` bytes at the new pointer that starts with `old` (the rest is
unspecified), carved from the heap (`avail' + esz·newCap ≤ avail`); the old
block and `F` unchanged; the scratch and spill bytes changed.

`Fk/RtCopy.lean` proves that a bump allocator satisfies this form
(`rt_growslice`). -/
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
