import Codec.Kind.EncodeFastPathAnyFrame
import Codec.Kind.DecodeAcceptNestedAnyFrame
import Runtime.Contracts

/-!
# Statement kinds for encoder fast-path theorems with nested Checkpoint fields, any frame

`encodeFastPathNestedKindAnyFrame C L fields` is the fast-path statement of `MarshalSSZTo` of a fixed-size container `C`
whose fields are flat fields (`NestedField.flat`) or pointers to a nested `Checkpoint` (`NestedField.checkpoint`).
**Fast path only**: premise `len(dst) + SizeSSZ ≤ cap(dst)`, every byte-vector field of its exact length and every
nested pointer not nil.
The `runtime.growslice` branches, the length rejects and the morestack path are not part of the statement.
The `newobject` branch of a nil pointer and the error wraps of the callee calls are also not part of it.

The kinds of `Codec/Kind/EncodeFastPathAnyFrame.lean` cover flat containers only.
These parts are different:

- The SSZ fields of the output are the leaves of `nestedInputFields fields`.
  A nested Checkpoint is two leaves: its epoch (8 bytes) and its root (32 bytes).
  One binder chunk holds the value of each leaf, and one chunk holds the old output bytes of each leaf.
- A nested Checkpoint field is one receiver word: the object pointer.
  The object holds the `state` word, the epoch, the root slice (pointer, 32, capacity word) and 32 more bytes.
  The root bytes are at the root pointer.
  Each nested field has two pointer binders (object and root) and the premise that the object pointer is not 0.
- The receiver words are only the words that the code reads.
  A byte-vector field is its pointer and its length; the capacity word and the `state` word are not named.
  `L.goStart` is the Go offset of the first field.
- The callee is used through its placement (`L.callees`).
  A proof of an instance uses `Prysm.Checkpoint.Encode.fast_path_function_spec_holds`.
- The stack below the return slot of a call is one block of `S + L.lowExtra` bytes.
  Its address is `rsp − (frame + 16 + lowExtra) − S`.
  A nested call uses the block as its callee frame.
  A `runtime.memmove` call of the function uses the top `S` bytes of the block as its scratch.
  The premises are `S < 2 ^ 60` and `MemmoveContract S`.
- A stack slot value can also be the frame pointer of the function (`rsp − 8`), which a callee saves.
  A boundary register can also hold 0, the error result of a callee.

The stack part is a parameter: the kind does not check that `L` is the frame of the code.
A proof of an instance checks the frame, and the generator rules check the callees.
The intermediate kinds `encodeHeadNestedKindAnyFrame`, `encodeFieldNestedKindAnyFrame` and `encodeEpilogueNestedKindAnyFrame`
have the same roles as the flat kinds.
-/

open Machine Runtime

open Codec
namespace Codec

/-- The content of a stack slot of a nested encoder state: an original chunk (`cs` index), the bytes of an entry
register, an existential chunk, the value of SSZ leaf `i`, the length `len + n`, a return address (directive index),
the low block of the entry state, the frame pointer `rsp − 8` of the function. -/
inductive NestedEncodeStackValue where
  | original (i : Nat)
  | reg (r : Reg64)
  | existential (i : Nat)
  | field (i : Nat)
  | len (n : Nat)
  | ret (n : Nat)
  | scratch
  | framePointer

/-- A stack slot: a value at an offset from the entry rsp, or a value at the low block address. -/
inductive NestedEncodeStackSlot where
  | at (o : StackOffset) (v : NestedEncodeStackValue)
  | low (v : NestedEncodeStackValue)

/-- The length of an existential chunk: a fixed length, `S` (the scratch of a callee) or `S + lowExtra` (the low block). -/
inductive NestedExistentialLength where
  | fixed (len : Nat)
  | low
  | lowBlock

/-- The frame facts of an encoder with nested Checkpoint fields (see the module text). `frame` = the `sub` amount. -/
structure EncoderNestedFrameLayout where
  callees : List Program
  goStart : Nat
  frame : Nat
  guardAddend : Nat
  lowExtra : Nat
  stackChunkCount : Nat
  stackChunkLengths : List (Nat × Nat)
  pre : List NestedEncodeStackSlot
  existentials : List NestedExistentialLength
  post : List NestedEncodeStackSlot

/-- Number of nested Checkpoint fields. -/
def checkpointCount : List NestedField → Nat
  | [] => 0
  | .checkpoint :: fs => checkpointCount fs + 1
  | .flat _ :: fs => checkpointCount fs

/-- Length of the binder group `xs`: the leaf values, three object chunks per nested field, `pre`, the old output of
each leaf. -/
def nestedEncodeBinderCount (fields : List NestedField) : Nat :=
  (nestedInputFields fields).length + 3 * checkpointCount fields + 1 + (nestedInputFields fields).length

/-- The object chunks of the binder group: per nested field the `state` word, the root capacity word and the 32 last bytes. -/
def nestedBindersObject (fields : List NestedField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (nestedInputFields fields).length
def nestedBindersPrefix (fields : List NestedField) (xs : List (List UInt8)) : List UInt8 :=
  xs.getD ((nestedInputFields fields).length + 3 * checkpointCount fields) []
def nestedBindersOverwritten (fields : List NestedField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop ((nestedInputFields fields).length + 3 * checkpointCount fields + 1)

/-- Length hypotheses of the object chunks: 8, 8 and 32 bytes for each nested field. -/
def objectLengthFacts : Nat → List (List UInt8) → List Prop
  | 0, _ => []
  | c + 1, cs => ((cs.headD []).length = 8) :: ((cs.tail.headD []).length = 8) :: ((cs.tail.tail.headD []).length = 32)
      :: objectLengthFacts c cs.tail.tail.tail

/-- Length hypotheses of the binder group (none for `pre`). -/
def nestedEncodeLengthFacts (fields : List NestedField) (xs : List (List UInt8)) : List Prop :=
  valueLengthFacts (nestedInputFields fields) xs
    ++ objectLengthFacts (checkpointCount fields) (nestedBindersObject fields xs)
    ++ valueLengthFacts (nestedInputFields fields) (nestedBindersOverwritten fields xs)

/-- The premises that the object pointers are not nil. -/
def nonNilFacts : List NestedField → List (BitVec 64) → List Prop
  | [], _ => []
  | .flat (.bytes _) :: fs, ps => nonNilFacts fs ps.tail
  | .flat .uint64 :: fs, ps => nonNilFacts fs ps
  | .checkpoint :: fs, ps => (ps.headD 0 ≠ 0) :: nonNilFacts fs ps.tail.tail

/-- The receiver words from Go offset `g`: the value of a `.uint64` field; pointer and length of a `.bytes` field;
the object pointer of a nested field. -/
def nestedEncodeReceiverChunks (b : BitVec 64) : List NestedField → Nat → List (List UInt8) → List (BitVec 64)
    → List (DataMem → Prop)
  | [], _, _, _ => []
  | .flat .uint64 :: fs, g, vs, ps => Eq ((vs.headD []).At (addOffset b g)) :: nestedEncodeReceiverChunks b fs (g + 8) vs.tail ps
  | .flat (.bytes n) :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 8)))
      :: nestedEncodeReceiverChunks b fs (g + 24) vs.tail ps.tail
  | .checkpoint :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g)) :: nestedEncodeReceiverChunks b fs (g + 8) vs.tail.tail ps.tail.tail

/-- The heap chunks: the content of each `.bytes` field at its pointer; each nested object and its root. -/
def nestedEncodeHeapChunks : List NestedField → List (List UInt8) → List (List UInt8) → List (BitVec 64)
    → List (DataMem → Prop)
  | [], _, _, _ => []
  | .flat (.bytes _) :: fs, vs, os, ps => Eq ((vs.headD []).At (ps.headD 0)) :: nestedEncodeHeapChunks fs vs.tail os ps.tail
  | .flat .uint64 :: fs, vs, os, ps => nestedEncodeHeapChunks fs vs.tail os ps
  | .checkpoint :: fs, vs, os, ps =>
    [Eq ((os.headD []).At (ps.headD 0)), Eq ((vs.headD []).At (ps.headD 0 + 8)),
     Eq ((Int.toBytes 8 (ps.tail.headD 0).toInt).At (ps.headD 0 + 16)), Eq ((Int.toBytes 8 32).At (ps.headD 0 + 24)),
     Eq ((os.tail.headD []).At (ps.headD 0 + 32)), Eq ((os.tail.tail.headD []).At (ps.headD 0 + 40)),
     Eq ((vs.tail.headD []).At (ps.tail.headD 0))]
      ++ nestedEncodeHeapChunks fs vs.tail.tail os.tail.tail.tail ps.tail.tail

/-- Length of the existential chunks. -/
def NestedExistentialLength.len (S x : Nat) : NestedExistentialLength → Nat
  | .fixed l => l
  | .low => S
  | .lowBlock => S + x

/-- Length facts of the existential chunks. -/
def nestedExistentialLengthFacts (S x : Nat) : List NestedExistentialLength → List (List UInt8) → List Prop
  | [], _ => []
  | e :: es, ys => ((ys.headD []).length = e.len S x) :: nestedExistentialLengthFacts S x es ys.tail

variable [Host]

/-- The bytes of a slot value. -/
def NestedEncodeStackValue.bytes (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8) :
    NestedEncodeStackValue → List UInt8
  | .original i => cs.getD i []
  | .reg r => Int.toBytes 8 (s.regs.get64 r).toInt
  | .existential i => ys.getD i []
  | .field i => vals.getD i []
  | .len n => Int.toBytes 8 (s.regs.rcx.toBitVec + BitVec.ofNat 64 n).toInt
  | .ret n => Int.toBytes 8 (Host.addrOf (k + n)).toBitVec.toInt
  | .scratch => scratch
  | .framePointer => Int.toBytes 8 (s.regs.rsp.toBitVec - 8).toInt

/-- The memory chunk of a stack slot; the low block is at `rsp − loB − S`. -/
def NestedEncodeStackSlot.chunk (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8)
    (S loB : Nat) : NestedEncodeStackSlot → DataMem → Prop
  | .at o v => Eq ((v.bytes k s cs ys vals scratch).At (o.addr s.regs.rsp.toBitVec))
  | .low v => Eq ((v.bytes k s cs ys vals scratch).At
      (s.regs.rsp.toBitVec - BitVec.ofNat 64 loB - BitVec.ofNat 64 S))

set_option linter.unusedVariables false in
/-- The binder prefix of every nested encoder fast-path kind: code placement, callee placements, the binder group and its
lengths, the pointers and the non-nil premises, the entry state, `hpre`, the stack chunks and their lengths, the frame `R`,
`S`, `S < 2 ^ 60` and the low block of `S + lowExtra` bytes. The body gets the hypothesis `MemmoveContract S`. -/
def nestedEncodeBinders (C : Program) (L : EncoderNestedFrameLayout) (fields : List NestedField)
    (body : Nat → List (List UInt8) → List (BitVec 64) → MachineData → UInt64 → UInt64 → List (List UInt8)
      → (DataMem → Prop) → Nat → List UInt8 → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllPlaced L.callees
  (ForallChunks (nestedEncodeBinderCount fields) (fun xs => Implications (nestedEncodeLengthFacts fields xs)
    (ForallWords (nestedPointerCount fields) (fun ps => Implications (nonNilFacts fields ps)
      (∀ (s : MachineData) (ra guard : UInt64),
      (nestedBindersPrefix fields xs).length = s.regs.rcx.toNat →
      ForallChunks L.stackChunkCount (fun cs => Implications (chunkLengthFacts L.stackChunkLengths cs)
        (∀ (R : DataMem → Prop) (S : Nat), S < 2 ^ 60 → ∀ (scratch : List UInt8), scratch.length = S + L.lowExtra →
          body k xs ps s ra guard cs R S scratch [MemmoveContract S])))))))

/-- The memory of a boundary state: stack slots `stk`, the first `done` fields written to the output. -/
def nestedEncodeMem (L : EncoderNestedFrameLayout) (fields : List NestedField) (stk : List NestedEncodeStackSlot) (done : Nat)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8)
    (ys : List (List UInt8)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (NestedEncodeStackSlot.chunk k s cs ys xs scratch S (L.frame + 16 + L.lowExtra))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ nestedEncodeReceiverChunks s.regs.rax.toBitVec fields L.goStart xs ps
      ++ nestedEncodeHeapChunks fields xs (nestedBindersObject fields xs) ps
      ++ [Eq ((nestedBindersPrefix fields xs).At s.regs.rbx.toBitVec)]
      ++ encodeOutputChunks (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec) (nestedInputFields fields) 0
          (nestedInputFields (fields.take done)).length xs (nestedBindersOverwritten fields xs)
      ++ [R])

/-- The fast-path post-state: `(dst, len + size, cap, nil)` and the output bytes. -/
def nestedEncodeFinalStatePredicate (L : EncoderNestedFrameLayout) (fields : List NestedField)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
    ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + sszSize (nestedInputFields fields) ∧ st.data.regs.rcx = s.regs.rdi
    ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
    ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
    ExistsChunks L.existentials.length (fun ys => Conjunctions (nestedExistentialLengthFacts S L.lowExtra L.existentials ys)
      (nestedEncodeMem L fields L.post fields.length k xs ps s ra guard cs R S scratch ys st.data.dmem))

set_option linter.unusedVariables false in
/-- **Fast-path statement kind of a container encoder with nested Checkpoint fields, any frame** (see the module text). -/
abbrev encodeFastPathNestedKindAnyFrame (C : Program) (L : EncoderNestedFrameLayout) (fields : List NestedField) : Prop :=
  nestedEncodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ nestedEncodeMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize (nestedInputFields fields) ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (Eventually (step1 Host.exe) (nestedEncodeFinalStatePredicate L fields k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

/-- What a register holds at a field boundary: the receiver, the `dst` pointer, the capacity, `len + n`, or 0. -/
inductive NestedEncodeRegisterValue where
  | receiver
  | ptr
  | cap
  | len (n : Nat)
  | zero

def NestedEncodeRegisterValue.val (s : MachineData) : NestedEncodeRegisterValue → BitVec 64
  | .receiver => s.regs.rax.toBitVec
  | .ptr => s.regs.rbx.toBitVec
  | .cap => s.regs.rdi.toBitVec
  | .len n => addOffset s.regs.rcx.toBitVec n
  | .zero => 0

/-- A boundary state of a generated-style fast-path proof with nested fields: directive index, number of encoded fields,
register facts, stack slots, existential chunks. -/
structure NestedEncodeBoundaryState where
  pc : Nat
  done : Nat
  regs : List (Reg64 × NestedEncodeRegisterValue)
  stackSlots : List NestedEncodeStackSlot
  existentials : List NestedExistentialLength

/-- Register facts of a boundary state. -/
def nestedEncodeRegisterFacts (s : MachineData) (st : MachineState) : List (Reg64 × NestedEncodeRegisterValue) → List Prop
  | [] => []
  | (r, v) :: rs => (st.data.regs.get64 r = v.val s) :: nestedEncodeRegisterFacts s st rs

/-- The state predicate of a boundary state. -/
def nestedEncodeBoundaryStatePredicate (L : EncoderNestedFrameLayout) (fields : List NestedField) (d : NestedEncodeBoundaryState)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 (L.frame + 8) }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    Conjunctions (nestedEncodeRegisterFacts s st d.regs)
      (ExistsChunks d.existentials.length (fun ys => Conjunctions (nestedExistentialLengthFacts S L.lowExtra d.existentials ys)
        (nestedEncodeMem L fields d.stackSlots d.done k xs ps s ra guard cs R S scratch ys st.data.dmem)))

set_option linter.unusedVariables false in
/-- Kind of the head theorem: fast-path premises, entry → boundary state `d0`. -/
abbrev encodeHeadNestedKindAnyFrame (C : Program) (L : EncoderNestedFrameLayout) (fields : List NestedField)
    (d0 : NestedEncodeBoundaryState) : Prop :=
  nestedEncodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ nestedEncodeMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize (nestedInputFields fields) ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (Eventually (step1 Host.exe) (nestedEncodeBoundaryStatePredicate L fields d0 k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem: boundary state `d` → boundary state `d'`, under the guard and capacity premises. -/
abbrev encodeFieldNestedKindAnyFrame (C : Program) (L : EncoderNestedFrameLayout) (fields : List NestedField)
    (d d' : NestedEncodeBoundaryState) : Prop :=
  nestedEncodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize (nestedInputFields fields) ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (∀ (st0 : MachineState), nestedEncodeBoundaryStatePredicate L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (nestedEncodeBoundaryStatePredicate L fields d' k xs ps s ra guard cs R S scratch) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem: boundary state `d` → the fast-path post-state. -/
abbrev encodeEpilogueNestedKindAnyFrame (C : Program) (L : EncoderNestedFrameLayout) (fields : List NestedField)
    (d : NestedEncodeBoundaryState) : Prop :=
  nestedEncodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize (nestedInputFields fields) ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
      (st0 : MachineState), nestedEncodeBoundaryStatePredicate L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (nestedEncodeFinalStatePredicate L fields k xs ps s ra guard cs R S scratch) st0)

end Codec
