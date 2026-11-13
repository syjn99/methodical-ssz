import Codec.Kind.DecodeAcceptComposition

/-!
# Statement kinds for whole accept theorems of flat decoders, any frame

`decAcceptKindAnyFrame C L fields` is the accept statement of a flat fixed-size container decoder `C`.
- `fields : List ContainerField` (`Codec/Kind/DecodeAcceptComposition.lean`): fixed byte vectors (`.bytes n`, a fresh slice, `len = cap = n`) and
  8-byte fields (`.u64`). A field decoded by a callee (`Slot`, `Epoch`, `ValidatorIndex`, `CommitteeIndex`
  `UnmarshalSSZ`) is `.u64` here: in the receiver and in the input it is the same as an inline `uint64`. The
  callee shows only as placement premises (`L.callees`).
- `L : DecoderFrameLayout`: the frame facts of the `.S` file. Stack chunk binders and length hypotheses (`stackChunkCount`,
  `stackChunkLengths`), the stack slots before (`pre`) and after (`post`, `existentials`), the runtime configuration (`runtime`: `none`
  for a decoder without `makeslice` / `memmove`), the stack-guard addend (`guardAddend`), the `state` word (`stateWord`).

The input chunks, the receiver words before and after, the heap chunks and the sizes are computed from
`fields` by the functions of `Codec/Kind/DecodeAcceptComposition.lean` (unchanged). The stack part is a parameter: the kind does
not check that `L` is the frame of the code; a proof of an instance does (a wrong slot does not close).
The kind does not check that `L.callees` are the callees of the fields: that is a rule of the generator.

The binder prefix (`decBinders`) is shared with the three kinds of the intermediate theorems of a generated
accept proof. These are stated over the WHOLE accept memory in entry-state terms:
- `decHeadKindAnyFrame C L fields d0`: accept premises, entry → boundary state `d0`;
- `decFieldKindAnyFrame C L fields d d'`: boundary state `d` → boundary state `d'` (one field);
- `decEpilogueKindAnyFrame C L fields d`: boundary state `d` → the accept post-state.
A boundary state `DecodeBoundaryState` gives the directive index, the number of decoded fields, register facts and the
stack slots; `decBoundaryStatePredicate` renders it. The accept proof chains the theorems with `eventually_trans` only.

Ties to the hand statements: `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- A stack offset from the entry rsp: `rsp + n` or `rsp - n`. -/
inductive StackOffset where
  | above (n : Nat)
  | below (n : Nat)

/-- The address of a stack offset. -/
def StackOffset.addr (b : BitVec 64) : StackOffset → BitVec 64
  | .above n => b + BitVec.ofNat 64 n
  | .below n => b - BitVec.ofNat 64 n

/-- The content of a stack slot: an original chunk (`cs` index), the bytes of an entry register, an
existential chunk, the pointer of a byte field (index among the byte fields), zero, or a return address
(directive index). -/
inductive StackValue where
  | original (i : Nat)
  | reg (r : Reg64)
  | existential (i : Nat)
  | ptr (i : Nat)
  | zero
  | ret (n : Nat)

/-- A stack slot: a value at an offset, or a value at the low-stack address `rsp - loB - S`. -/
inductive StackSlot where
  | at (o : StackOffset) (v : StackValue)
  | low (v : StackValue)

/-- Length of an existential chunk: a number, or the low-stack length. -/
inductive ExistentialLength where
  | fixed (len : Nat)
  | low

/-- Runtime configuration of a decoder with `makeslice` / `memmove` calls: premise `S < 2 ^ 60` (`scratchBound`), the
low-stack chunk has `S + x` bytes (`x = 0`: `S`), its index among the stack chunks, its address
`rsp - loB - S`. -/
structure RuntimeConfig where
  scratchBound : Bool
  lowExtra : Nat
  lowIndex : Nat
  lowOffset : Nat

/-- The frame facts of a decoder (see the module text). `frame` = entry rsp − rsp inside the body. -/
structure DecoderFrameLayout where
  callees : List Program
  stackChunkCount : Nat
  stackChunkLengths : List (Nat × Nat)
  pre : List StackSlot
  runtime : Option RuntimeConfig
  guardAddend : Nat
  stateWord : Bool
  existentials : List ExistentialLength
  post : List StackSlot
  frame : Nat

/-- `a` for 0, else `a + x`. -/
def addExtra (a : Nat) : Nat → Nat
  | 0 => a
  | x + 1 => a + (x + 1)

/-- `∃ x₁ … xₘ : List UInt8, P [x₁, …, xₘ]`. -/
def ExistsChunks : Nat → (List (List UInt8) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∃ x : List UInt8, ExistsChunks m (fun xs => P (x :: xs))

/-- `A₁ ∧ … ∧ Aₘ ∧ Q`. -/
def Conjunctions : List Prop → Prop → Prop
  | [], Q => Q
  | A :: As, Q => A ∧ Conjunctions As Q

/-- Length hypotheses `(cs[i]).length = l` of the stack chunks. -/
def chunkLengthFacts : List (Nat × Nat) → List (List UInt8) → List Prop
  | [], _ => []
  | (i, l) :: r, cs => ((cs.getD i []).length = l) :: chunkLengthFacts r cs

/-- `[S < 2 ^ 60]` or nothing. -/
def scratchBoundFacts : Bool → Nat → List Prop
  | true, S => [S < 2 ^ 60]
  | false, _ => []

def ExistentialLength.len (S x : Nat) : ExistentialLength → Nat
  | .fixed l => l
  | .low => addExtra S x

/-- Length facts of the existential chunks. -/
def existentialLengthFacts (S x : Nat) : List ExistentialLength → List (List UInt8) → List Prop
  | [], _ => []
  | e :: es, xs => ((xs.headD []).length = e.len S x) :: existentialLengthFacts S x es xs.tail

def RuntimeConfig.lowExtraOf : Option RuntimeConfig → Nat
  | none => 0
  | some c => c.lowExtra

def RuntimeConfig.lowOffsetOf : Option RuntimeConfig → Nat
  | none => 0
  | some c => c.lowOffset

variable [Host]

/-- `∀ (kP : Nat) (hkP : P.IsInfixAt Host.prog kP) (hfP : LabelsFresh P kP), …` for every callee program. -/
def AllPlaced : List Program → Prop → Prop
  | [], Q => Q
  | P :: Ps, Q => ∀ (kP : Nat) (_ : P.IsInfixAt Host.prog kP) (_ : LabelsFresh P kP), AllPlaced Ps Q

/-- The bytes of a slot value. -/
def StackValue.bytes (k : Nat) (s : MachineData) (cs xs : List (List UInt8)) (ps : List (BitVec 64)) : StackValue → List UInt8
  | .original i => cs.getD i []
  | .reg r => Int.toBytes 8 (s.regs.get64 r).toInt
  | .existential i => xs.getD i []
  | .ptr i => Int.toBytes 8 (ps.getD i 0).toInt
  | .zero => Int.toBytes 8 (0 : UInt64).toBitVec.toInt
  | .ret n => Int.toBytes 8 (Host.addrOf (k + n)).toBitVec.toInt

/-- The memory chunk of a stack slot. -/
def StackSlot.chunk (k : Nat) (s : MachineData) (cs xs : List (List UInt8)) (ps : List (BitVec 64)) (S loB : Nat) :
    StackSlot → DataMem → Prop
  | .at o v => Eq ((v.bytes k s cs xs ps).At (o.addr s.regs.rsp.toBitVec))
  | .low v => Eq ((v.bytes k s cs xs ps).At (s.regs.rsp.toBitVec - BitVec.ofNat 64 loB - BitVec.ofNat 64 S))

/-- The runtime binders: nothing (`none`), or `S`, `scratchBound`, `hlo`, `Heap`, `avail`. The body gets `S`, the heap
chunk after `h` used bytes, the `writeBarrier` chunk and the hypotheses `hav hms hmm`. -/
def runtimeBinders (rt : Option RuntimeConfig) (hsz : Nat) (cs : List (List UInt8))
    (body : Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  match rt with
  | none => body 0 (fun _ => []) [] []
  | some c => ∀ (S : Nat), Implications (scratchBoundFacts c.scratchBound S) ((cs.getD c.lowIndex []).length = addExtra S c.lowExtra →
      ∀ (Heap : Nat → DataMem → Prop) (avail : Nat),
        body S (fun h => [Heap (avail - h)]) [Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)]
          [hsz ≤ avail, MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (addExtra S c.lowExtra), MemmoveContract (addExtra S c.lowExtra)])

set_option linter.unusedVariables false in
/-- The binder prefix of every whole-accept kind: code placement, callee placements, field values and their lengths,
entry state, stack and receiver chunks and their lengths, the frame `R`, the runtime binders. -/
def decBinders (C : Program) (L : DecoderFrameLayout) (fields : List ContainerField)
    (body : Nat → List (List UInt8) → MachineData → UInt64 → UInt64 → List (List UInt8) → (DataMem → Prop)
      → Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllPlaced L.callees
  (ForallChunks fields.length (fun vs => Implications (valueLengthFacts fields vs)
    (∀ (s : MachineData) (ra guard : UInt64),
    ForallChunks (L.stackChunkCount + stateWords L.stateWord + receiverWords fields) (fun cs =>
      Implications (chunkLengthFacts L.stackChunkLengths cs ++ wordLengthFacts (stateWords L.stateWord + receiverWords fields) (cs.drop L.stackChunkCount))
      (∀ (R : DataMem → Prop), runtimeBinders L.runtime (heapSize fields) cs (fun S heapAt wb hyps =>
        body k vs s ra guard cs R S heapAt wb hyps))))))

/-- The memory of a boundary state: stack slots `stackSlots`, the first `done` fields decoded. -/
def decMem (L : DecoderFrameLayout) (fields : List ContainerField) (stk : List StackSlot) (done : Nat)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop))
    (xs : List (List UInt8)) (ps : List (BitVec 64)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (StackSlot.chunk k s cs xs ps S (RuntimeConfig.lowOffsetOf L.runtime))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ heapAt (heapSize (fields.take done))
      ++ inputChunks s.regs.rbx.toBitVec fields 0 vs
      ++ stateChunk s.regs.rax.toBitVec L.stateWord (cs.drop L.stackChunkCount)
      ++ receiverPost s.regs.rax.toBitVec (fields.take done) (8 * stateWords L.stateWord) vs ps
      ++ receiverPre s.regs.rax.toBitVec (receiverWords (fields.drop done))
          (8 * stateWords L.stateWord + 8 * receiverWords (fields.take done))
          (cs.drop (L.stackChunkCount + stateWords L.stateWord + receiverWords (fields.take done)))
      ++ heapPost (fields.take done) vs ps
      ++ wb ++ [R])

/-- The accept post-state. -/
def decFinalStatePredicate (L : DecoderFrameLayout) (fields : List ContainerField)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st' => st'.pc = Int64.ofBitVec ra.toBitVec ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
    ∧ st'.data.regs.rsp = s.regs.rsp + 8 ∧ st'.data.regs.rbp = s.regs.rbp
    ∧ st'.data.regs.r14 = s.regs.r14 ∧
    ExistsWords (countBytesFields fields) (fun ps => ExistsChunks L.existentials.length (fun xs => Conjunctions (existentialLengthFacts S (RuntimeConfig.lowExtraOf L.runtime) L.existentials xs)
      (decMem L fields L.post fields.length k vs s ra guard cs R S heapAt wb xs ps st'.data.dmem)))

set_option linter.unusedVariables false in
/-- **Accept statement kind of a flat container decoder, any frame** (see the module text). -/
abbrev decAcceptKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List ContainerField) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ decMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize fields)),
      Implications hyps (Eventually (step1 Host.exe) (decFinalStatePredicate L fields k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

/-- What a register holds at a field boundary: the receiver, the buffer, or zero. -/
inductive DecodeRegisterValue where
  | receiver
  | buffer
  | zero

def DecodeRegisterValue.val (s : MachineData) : DecodeRegisterValue → BitVec 64
  | .receiver => s.regs.rax.toBitVec
  | .buffer => s.regs.rbx.toBitVec
  | .zero => 0

/-- A boundary state of a generated accept proof: directive index, number of decoded fields, register facts,
stack slots, existential chunks. -/
structure DecodeBoundaryState where
  pc : Nat
  done : Nat
  regs : List (Reg64 × DecodeRegisterValue)
  stackSlots : List StackSlot
  existentials : List ExistentialLength

/-- Register facts of a boundary state. -/
def decodeRegisterFacts (s : MachineData) (st : MachineState) : List (Reg64 × DecodeRegisterValue) → List Prop
  | [] => []
  | (r, v) :: rs => (st.data.regs.get64 r = v.val s) :: decodeRegisterFacts s st rs

/-- The state predicate of a boundary state. -/
def decBoundaryStatePredicate (L : DecoderFrameLayout) (fields : List ContainerField) (d : DecodeBoundaryState)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 L.frame }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    Conjunctions (decodeRegisterFacts s st d.regs)
      (ExistsWords (countBytesFields (fields.take d.done)) (fun ps => ExistsChunks d.existentials.length (fun xs =>
        Conjunctions (existentialLengthFacts S (RuntimeConfig.lowExtraOf L.runtime) d.existentials xs)
          (decMem L fields d.stackSlots d.done k vs s ra guard cs R S heapAt wb xs ps st.data.dmem))))

set_option linter.unusedVariables false in
/-- Kind of the head theorem of a generated accept proof: accept premises, entry → boundary state `d0`. -/
abbrev decHeadKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List ContainerField) (d0 : DecodeBoundaryState) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ decMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize fields)),
      Implications hyps (Eventually (step1 Host.exe) (decBoundaryStatePredicate L fields d0 k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem of a generated accept proof: boundary state `d` → boundary state `d'`. -/
abbrev decFieldKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List ContainerField) (d d' : DecodeBoundaryState) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat),
      Implications hyps (∀ (st0 : MachineState), decBoundaryStatePredicate L fields d k vs s ra guard cs R S heapAt wb st0 →
        Eventually (step1 Host.exe) (decBoundaryStatePredicate L fields d' k vs s ra guard cs R S heapAt wb) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem of a generated accept proof: boundary state `d` → the accept post-state. -/
abbrev decEpilogueKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List ContainerField) (d : DecodeBoundaryState) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (st0 : MachineState), decBoundaryStatePredicate L fields d k vs s ra guard cs R S heapAt wb st0 →
      Eventually (step1 Host.exe) (decFinalStatePredicate L fields k vs s ra guard cs R S heapAt wb) st0)

end Codec
