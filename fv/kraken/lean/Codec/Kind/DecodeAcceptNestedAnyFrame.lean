import Codec.Kind.DecodeAcceptAnyFrame
import Runtime.NewobjectContract

/-!
# Statement kinds for whole accept theorems of decoders with nested Checkpoint fields, any frame

`decodeAcceptNestedKindAnyFrame C L fields` is the accept statement of a fixed-size container decoder `C` whose fields are
flat fields (`NestedField.flat`, a `ContainerField`) or pointers to a nested `Checkpoint` (`NestedField.checkpoint`).
The kinds of `Codec/Kind/DecodeAcceptAnyFrame.lean` cover flat containers only.
This module keeps their frame language (`DecoderFrameLayout`, `StackSlot`, `StackValue`) and their list functions.
These parts change:

- The input of a nested Checkpoint field is its two SSZ fields: the epoch (8 bytes) and the root (32 bytes).
  So the field values are the values of `nestedInputFields fields`.
- The receiver word of a nested field is the pointer to a new 72-byte object.
  The object holds `state` = 0, the epoch, a new 32-byte root slice (pointer, 32, 32) and 32 zero bytes
  (`unknownFields`, `sizeCache` and the padding).
  The root bytes are at the root pointer.
- A nested field has two pointer existentials: the object and the root.
  A flat byte field has one.
- The runtime binders add `8 ≤ S` and the contracts of the nested callee.
  The callee needs `MakesliceContract … S` and `MemmoveContract S`.
  This function needs `MakesliceContract … (S + x)`, `MemmoveContract (S + x)` and
  `NewobjectContract Heap typeCheckpoint 72 (S + x)`, with `x` = `L.runtime.lowExtra`.

The kind does not check that `L` is the frame of the code, or that `L.callees` are the callees of the fields.
A proof of an instance checks the frame, and the generator rules check the callees.
The intermediate kinds `decodeHeadNestedKindAnyFrame`, `decodeFieldNestedKindAnyFrame` and `decodeEpilogueNestedKindAnyFrame`
have the same roles as the flat kinds.
-/

open Machine Runtime

open Codec
namespace Codec

/-- A field of a container decoder with nested containers: a flat field, or a pointer to a nested `Checkpoint`. -/
inductive NestedField where
  | flat (f : ContainerField)
  | checkpoint

namespace NestedField

/-- The SSZ fields of the input of the field: a nested Checkpoint is its epoch and its root. -/
def inputFields : NestedField → List ContainerField
  | flat f => [f]
  | checkpoint => [.uint64, .bytes 32]

/-- Number of 8-byte receiver words. -/
def words : NestedField → Nat
  | flat f => f.words
  | checkpoint => 1

/-- Heap bytes used by the decoder for the field: the 72-byte object and the 32-byte root of a nested Checkpoint. -/
def heap : NestedField → Nat
  | flat f => f.heap
  | checkpoint => 104

/-- Number of pointer existentials. -/
def pointers : NestedField → Nat
  | flat (.bytes _) => 1
  | flat .uint64 => 0
  | checkpoint => 2

end NestedField

/-- The SSZ fields of the input, in order. -/
def nestedInputFields : List NestedField → List ContainerField
  | [] => []
  | f :: fs => f.inputFields ++ nestedInputFields fs

def nestedHeapSize (fs : List NestedField) : Nat := fs.foldl (fun a f => a + f.heap) 0
def nestedReceiverWords (fs : List NestedField) : Nat := fs.foldl (fun a f => a + f.words) 0
def nestedPointerCount (fs : List NestedField) : Nat := fs.foldl (fun a f => a + f.pointers) 0

/-- The chunks of a new Checkpoint object at `po` with the epoch `e8` and the root `root` at `pr`. -/
def checkpointObjectChunks (po pr : BitVec 64) (e8 root : List UInt8) : List (DataMem → Prop) :=
  [Eq ((List.replicate 8 0).At po), Eq (e8.At (po + 8)), Eq ((Int.toBytes 8 pr.toInt).At (po + 16)),
   Eq ((Int.toBytes 8 32).At (po + 24)), Eq ((Int.toBytes 8 32).At (po + 32)),
   Eq ((List.replicate 32 0).At (po + 40)), Eq (root.At pr)]

/-- The receiver words after the call: a slice header, the 8 value bytes, or the pointer of a nested object. -/
def nestedReceiverPost (b : BitVec 64) : List NestedField → Nat → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _, _ => []
  | .flat (.bytes n) :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 8)))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 16)))
      :: nestedReceiverPost b fs (g + 24) vs.tail ps.tail
  | .flat .uint64 :: fs, g, vs, ps => Eq ((vs.headD []).At (addOffset b g)) :: nestedReceiverPost b fs (g + 8) vs.tail ps
  | .checkpoint :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g)) :: nestedReceiverPost b fs (g + 8) vs.tail.tail ps.tail.tail

/-- The new heap chunks: the bytes of each byte field at its pointer, and each nested object with its root. -/
def nestedHeapPost : List NestedField → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _ => []
  | .flat (.bytes _) :: fs, vs, ps => Eq ((vs.headD []).At (ps.headD 0)) :: nestedHeapPost fs vs.tail ps.tail
  | .flat .uint64 :: fs, vs, ps => nestedHeapPost fs vs.tail ps
  | .checkpoint :: fs, vs, ps =>
    checkpointObjectChunks (ps.headD 0) (ps.tail.headD 0) (vs.headD []) (vs.tail.headD [])
      ++ nestedHeapPost fs vs.tail.tail ps.tail.tail

variable [Host]

/-- The runtime binders of a decoder with nested Checkpoint fields: nothing (`none`), or `S`, `8 ≤ S`,
`scratchBound`, `hlo`, `Heap`, `avail`. The body gets `S`, the heap chunk after `h` used bytes, the `writeBarrier`
chunk and the hypotheses: the heap size, the contracts of the nested callee (at `S`) and of this function (at `S + x`). -/
def nestedRuntimeBinders (rt : Option RuntimeConfig) (hsz : Nat) (cs : List (List UInt8))
    (body : Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  match rt with
  | none => body 0 (fun _ => []) [] []
  | some c => ∀ (S : Nat), 8 ≤ S → Implications (scratchBoundFacts c.scratchBound S)
      ((cs.getD c.lowIndex []).length = addExtra S c.lowExtra →
      ∀ (Heap : Nat → DataMem → Prop) (avail : Nat),
        body S (fun h => [Heap (avail - h)]) [Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)]
          [hsz ≤ avail, MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S, MemmoveContract S,
           MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 (addExtra S c.lowExtra),
           MemmoveContract (addExtra S c.lowExtra),
           NewobjectContract Heap ElfData.PrysmTarget.typeCheckpoint_addr 72 (addExtra S c.lowExtra)])

set_option linter.unusedVariables false in
/-- The binder prefix of every nested whole-accept kind: code placement, callee placements, field values and their
lengths, entry state, stack and receiver chunks and their lengths, the frame `R`, the runtime binders. -/
def nestedDecodeBinders (C : Program) (L : DecoderFrameLayout) (fields : List NestedField)
    (body : Nat → List (List UInt8) → MachineData → UInt64 → UInt64 → List (List UInt8) → (DataMem → Prop)
      → Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllPlaced L.callees
  (ForallChunks (nestedInputFields fields).length (fun vs => Implications (valueLengthFacts (nestedInputFields fields) vs)
    (∀ (s : MachineData) (ra guard : UInt64),
    ForallChunks (L.stackChunkCount + stateWords L.stateWord + nestedReceiverWords fields) (fun cs =>
      Implications (chunkLengthFacts L.stackChunkLengths cs
        ++ wordLengthFacts (stateWords L.stateWord + nestedReceiverWords fields) (cs.drop L.stackChunkCount))
      (∀ (R : DataMem → Prop), nestedRuntimeBinders L.runtime (nestedHeapSize fields) cs (fun S heapAt wb hyps =>
        body k vs s ra guard cs R S heapAt wb hyps))))))

/-- The memory of a boundary state: stack slots `stk`, the first `done` fields decoded. -/
def nestedDecodeMem (L : DecoderFrameLayout) (fields : List NestedField) (stk : List StackSlot) (done : Nat)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop))
    (xs : List (List UInt8)) (ps : List (BitVec 64)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (StackSlot.chunk k s cs xs ps S (RuntimeConfig.lowOffsetOf L.runtime))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ heapAt (nestedHeapSize (fields.take done))
      ++ inputChunks s.regs.rbx.toBitVec (nestedInputFields fields) 0 vs
      ++ stateChunk s.regs.rax.toBitVec L.stateWord (cs.drop L.stackChunkCount)
      ++ nestedReceiverPost s.regs.rax.toBitVec (fields.take done) (8 * stateWords L.stateWord) vs ps
      ++ receiverPre s.regs.rax.toBitVec (nestedReceiverWords (fields.drop done))
          (8 * stateWords L.stateWord + 8 * nestedReceiverWords (fields.take done))
          (cs.drop (L.stackChunkCount + stateWords L.stateWord + nestedReceiverWords (fields.take done)))
      ++ nestedHeapPost (fields.take done) vs ps
      ++ wb ++ [R])

/-- The accept post-state. -/
def nestedDecodeFinalStatePredicate (L : DecoderFrameLayout) (fields : List NestedField)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st' => st'.pc = Int64.ofBitVec ra.toBitVec ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
    ∧ st'.data.regs.rsp = s.regs.rsp + 8 ∧ st'.data.regs.rbp = s.regs.rbp
    ∧ st'.data.regs.r14 = s.regs.r14 ∧
    ExistsWords (nestedPointerCount fields) (fun ps => ExistsChunks L.existentials.length (fun xs =>
      Conjunctions (existentialLengthFacts S (RuntimeConfig.lowExtraOf L.runtime) L.existentials xs)
      (nestedDecodeMem L fields L.post fields.length k vs s ra guard cs R S heapAt wb xs ps st'.data.dmem)))

set_option linter.unusedVariables false in
/-- **Accept statement kind of a container decoder with nested Checkpoint fields, any frame** (see the module text). -/
abbrev decodeAcceptNestedKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List NestedField) : Prop :=
  nestedDecodeBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ nestedDecodeMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize (nestedInputFields fields))),
      Implications hyps (Eventually (step1 Host.exe) (nestedDecodeFinalStatePredicate L fields k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

/-- The state predicate of a boundary state. -/
def nestedDecodeBoundaryStatePredicate (L : DecoderFrameLayout) (fields : List NestedField) (d : DecodeBoundaryState)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 L.frame }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    Conjunctions (decodeRegisterFacts s st d.regs)
      (ExistsWords (nestedPointerCount (fields.take d.done)) (fun ps => ExistsChunks d.existentials.length (fun xs =>
        Conjunctions (existentialLengthFacts S (RuntimeConfig.lowExtraOf L.runtime) d.existentials xs)
          (nestedDecodeMem L fields d.stackSlots d.done k vs s ra guard cs R S heapAt wb xs ps st.data.dmem))))

set_option linter.unusedVariables false in
/-- Kind of the head theorem of a generated accept proof with nested fields: accept premises, entry → boundary state `d0`. -/
abbrev decodeHeadNestedKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List NestedField) (d0 : DecodeBoundaryState) : Prop :=
  nestedDecodeBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ nestedDecodeMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize (nestedInputFields fields))),
      Implications hyps (Eventually (step1 Host.exe) (nestedDecodeBoundaryStatePredicate L fields d0 k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem of a generated accept proof with nested fields: boundary state `d` → boundary state `d'`. -/
abbrev decodeFieldNestedKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List NestedField) (d d' : DecodeBoundaryState) : Prop :=
  nestedDecodeBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat),
      Implications hyps (∀ (st0 : MachineState), nestedDecodeBoundaryStatePredicate L fields d k vs s ra guard cs R S heapAt wb st0 →
        Eventually (step1 Host.exe) (nestedDecodeBoundaryStatePredicate L fields d' k vs s ra guard cs R S heapAt wb) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem of a generated accept proof with nested fields: boundary state `d` → the accept post-state. -/
abbrev decodeEpilogueNestedKindAnyFrame (C : Program) (L : DecoderFrameLayout) (fields : List NestedField) (d : DecodeBoundaryState) : Prop :=
  nestedDecodeBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (st0 : MachineState), nestedDecodeBoundaryStatePredicate L fields d k vs s ra guard cs R S heapAt wb st0 →
      Eventually (step1 Host.exe) (nestedDecodeFinalStatePredicate L fields k vs s ra guard cs R S heapAt wb) st0)

end Codec
