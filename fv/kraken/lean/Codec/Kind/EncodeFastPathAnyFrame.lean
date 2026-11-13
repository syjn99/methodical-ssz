import Codec.Kind.DecodeAcceptAnyFrame

/-!
# Statement kinds for encoder fast-path theorems of flat containers, any frame

`encodeFastPathKindAnyFrame C L fields` is the fast-path statement of `MarshalSSZTo` of a flat fixed-size container `C`.
**Fast path only**: premise `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact length.
The `runtime.growslice` branches, the length rejects and the morestack path are not part of the statement.

- `fields : List ContainerField` (`Codec/Kind/DecodeAcceptComposition.lean`): `.bytes n` = a `[]byte` field of SSZ size `n` (receiver words:
  pointer, length `n`, capacity word); `.uint64` = an 8-byte field (`uint64` or an overlay type of it).
- `L : EncoderFrameLayout`: the frame facts of the `.S` file. `stateWord` (the receiver has the protoc `state` word), `frame`
  (the `sub` amount `F`), `guardAddend` (stack-guard addend: 0 for the small guard, `N` of `lea -N(%rsp),%r12`), `callsMemmove`
  (the function calls `runtime.memmove`: binders `S scratch`, premise `MemmoveContract S`), the stack chunk binders
  and their lengths (`stackChunkCount`, `stackChunkLengths`), the stack slots before (`pre`) and after (`post`, `existentials`).

Binder group `xs` (one list): `[ast]` (if `stateWord`), the values of the `.uint64` fields, the capacity words of the
`.bytes` fields, the contents of the `.bytes` fields, `pre` (the bytes already in `dst`), one chunk `d` per
field (the bytes of `dst[len:cap]` the field overwrites). `ps`: the pointers of the `.bytes` fields.

The receiver chunks, the content chunks, the output chunks and the sizes are computed from `fields` alone.
The stack part is a parameter: the kind does not check that `L` is the frame of the code; a proof of an
instance does (a wrong slot does not close). The premise `cap < 2 ^ 63` is kept from the hand statements.

The binder prefix (`encodeBinders`) is shared with the three kinds of the intermediate theorems of a
generated-style proof, stated over the WHOLE memory in entry-state terms (the form of `Codec/Kind/DecodeAcceptAnyFrame.lean`):
- `encodeHeadKindAnyFrame C L fields d0`: fast-path premises, entry → boundary state `d0`;
- `encodeFieldKindAnyFrame C L fields d d'`: boundary state `d` → boundary state `d'` (one field);
- `encodeEpilogueKindAnyFrame C L fields d`: boundary state `d` → the post-state.
A boundary state `EncodeBoundaryState` gives the directive index, the number of encoded fields, register facts and the
stack slots; `encodeBoundaryStatePredicate` renders it. Ties to the hand statements: `Prysm/<Type>/EncodeFastPathKindInstances.lean` of BeaconBlockHeader, Eth1Data and Checkpoint.
-/

open Machine Runtime

open Codec
namespace Codec

/-- The content of a stack slot of an encoder state: an original chunk (`cs` index), the bytes of an entry
register, an existential chunk, the value of field `i`, the length `len + n`, a return address (directive
index), the scratch chunk below the `memmove` return slot. -/
inductive EncodeStackValue where
  | original (i : Nat)
  | reg (r : Reg64)
  | existential (i : Nat)
  | field (i : Nat)
  | len (n : Nat)
  | ret (n : Nat)
  | scratch

/-- A stack slot: a value at an offset from the entry rsp, or a value at `rsp - (frame + 16) - S`. -/
inductive EncodeStackSlot where
  | at (o : StackOffset) (v : EncodeStackValue)
  | low (v : EncodeStackValue)

/-- The frame facts of an encoder (see the module text). `frame` = the `sub` amount. -/
structure EncoderFrameLayout where
  stateWord : Bool
  frame : Nat
  guardAddend : Nat
  callsMemmove : Bool
  stackChunkCount : Nat
  stackChunkLengths : List (Nat × Nat)
  pre : List EncodeStackSlot
  existentials : List ExistentialLength
  post : List EncodeStackSlot

/-- `∀ p₁ … pₘ : BitVec 64, P [p₁, …, pₘ]`. -/
def ForallWords : Nat → (List (BitVec 64) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∀ p : BitVec 64, ForallWords m (fun ps => P (p :: ps))

/-- Number of `.uint64` fields. -/
def countUint64Fields : List ContainerField → Nat
  | [] => 0
  | .uint64 :: fs => countUint64Fields fs + 1
  | .bytes _ :: fs => countUint64Fields fs

/-- Length of the binder group `xs`. -/
def encodeBinderCount (st : Bool) (fields : List ContainerField) : Nat :=
  stateWords st + countUint64Fields fields + 2 * countBytesFields fields + 1 + fields.length

/-- The parts of the binder group. -/
def bindersUint64 (st : Bool) (xs : List (List UInt8)) : List (List UInt8) := xs.drop (stateWords st)
def bindersCapacity (st : Bool) (fields : List ContainerField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stateWords st + countUint64Fields fields)
def bindersContent (st : Bool) (fields : List ContainerField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stateWords st + countUint64Fields fields + countBytesFields fields)
def bindersPrefix (st : Bool) (fields : List ContainerField) (xs : List (List UInt8)) : List UInt8 :=
  xs.getD (stateWords st + countUint64Fields fields + 2 * countBytesFields fields) []
def bindersOverwritten (st : Bool) (fields : List ContainerField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stateWords st + countUint64Fields fields + 2 * countBytesFields fields + 1)

/-- Length hypotheses of the contents of the `.bytes` fields. -/
def contentLengthFacts : List ContainerField → List (List UInt8) → List Prop
  | [], _ => []
  | .bytes n :: fs, bs => ((bs.headD []).length = n) :: contentLengthFacts fs bs.tail
  | .uint64 :: fs, bs => contentLengthFacts fs bs

/-- Length hypotheses of the binder group (none for `pre`). -/
def encodeLengthFacts (st : Bool) (fields : List ContainerField) (xs : List (List UInt8)) : List Prop :=
  wordLengthFacts (stateWords st + countUint64Fields fields + countBytesFields fields) xs
    ++ contentLengthFacts fields (bindersContent st fields xs)
    ++ valueLengthFacts fields (bindersOverwritten st fields xs)

/-- The field values in field order (`us`: the `.uint64` values, `bs`: the `.bytes` contents). -/
def fieldValues : List ContainerField → List (List UInt8) → List (List UInt8) → List (List UInt8)
  | [], _, _ => []
  | .uint64 :: fs, us, bs => us.headD [] :: fieldValues fs us.tail bs
  | .bytes _ :: fs, us, bs => bs.headD [] :: fieldValues fs us bs.tail

/-- The receiver words from Go offset `g`: the value of a `.uint64` field; pointer, length and capacity word of
a `.bytes` field. -/
def encodeReceiverChunks (b : BitVec 64) : List ContainerField → Nat → List (List UInt8) → List (List UInt8) → List (BitVec 64)
    → List (DataMem → Prop)
  | [], _, _, _, _ => []
  | .uint64 :: fs, g, us, cs, ps => Eq ((us.headD []).At (addOffset b g)) :: encodeReceiverChunks b fs (g + 8) us.tail cs ps
  | .bytes n :: fs, g, us, cs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOffset b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOffset b (g + 8)))
      :: Eq ((cs.headD []).At (addOffset b (g + 16)))
      :: encodeReceiverChunks b fs (g + 24) us cs.tail ps.tail

/-- The contents of the `.bytes` fields at their pointers. -/
def encodeContentChunks : List ContainerField → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _ => []
  | .uint64 :: fs, bs, ps => encodeContentChunks fs bs ps
  | .bytes _ :: fs, bs, ps => Eq ((bs.headD []).At (ps.headD 0)) :: encodeContentChunks fs bs.tail ps.tail

/-- The output chunks from SSZ offset `o`: the value of each of the first `done` fields, the old chunk `d` of
the others. -/
def encodeOutputChunks (b : BitVec 64) : List ContainerField → Nat → Nat → List (List UInt8) → List (List UInt8)
    → List (DataMem → Prop)
  | [], _, _, _, _ => []
  | f :: fs, o, 0, vals, ds => Eq ((ds.headD []).At (addOffset b o)) :: encodeOutputChunks b fs (o + f.size) 0 vals.tail ds.tail
  | f :: fs, o, d + 1, vals, ds =>
    Eq ((vals.headD []).At (addOffset b o)) :: encodeOutputChunks b fs (o + f.size) d vals.tail ds.tail

variable [Host]

/-- The bytes of a slot value. -/
def EncodeStackValue.bytes (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8) :
    EncodeStackValue → List UInt8
  | .original i => cs.getD i []
  | .reg r => Int.toBytes 8 (s.regs.get64 r).toInt
  | .existential i => ys.getD i []
  | .field i => vals.getD i []
  | .len n => Int.toBytes 8 (s.regs.rcx.toBitVec + BitVec.ofNat 64 n).toInt
  | .ret n => Int.toBytes 8 (Host.addrOf (k + n)).toBitVec.toInt
  | .scratch => scratch

/-- The memory chunk of a stack slot. -/
def EncodeStackSlot.chunk (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8)
    (S loB : Nat) : EncodeStackSlot → DataMem → Prop
  | .at o v => Eq ((v.bytes k s cs ys vals scratch).At (o.addr s.regs.rsp.toBitVec))
  | .low v => Eq ((v.bytes k s cs ys vals scratch).At
      (s.regs.rsp.toBitVec - BitVec.ofNat 64 loB - BitVec.ofNat 64 S))

/-- The `memmove` binders: nothing, or `S`, `scratch`, `hsc`; the body gets the hypothesis `MemmoveContract S`. -/
def encodeRuntimeBinders (rt : Bool) (body : Nat → List UInt8 → List Prop → Prop) : Prop :=
  match rt with
  | false => body 0 [] []
  | true => ∀ (S : Nat) (scratch : List UInt8), scratch.length = S → body S scratch [MemmoveContract S]

set_option linter.unusedVariables false in
/-- The binder prefix of every encoder fast-path kind: code placement, the binder group and its lengths, the field
pointers, the entry state, `hpre`, the stack chunks and their lengths, the frame `R`, the `memmove` binders. -/
def encodeBinders (C : Program) (L : EncoderFrameLayout) (fields : List ContainerField)
    (body : Nat → List (List UInt8) → List (BitVec 64) → MachineData → UInt64 → UInt64 → List (List UInt8)
      → (DataMem → Prop) → Nat → List UInt8 → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  ForallChunks (encodeBinderCount L.stateWord fields) (fun xs => Implications (encodeLengthFacts L.stateWord fields xs)
    (ForallWords (countBytesFields fields) (fun ps => ∀ (s : MachineData) (ra guard : UInt64),
      (bindersPrefix L.stateWord fields xs).length = s.regs.rcx.toNat →
      ForallChunks L.stackChunkCount (fun cs => Implications (chunkLengthFacts L.stackChunkLengths cs)
        (∀ (R : DataMem → Prop), encodeRuntimeBinders L.callsMemmove (fun S scratch hyps =>
          body k xs ps s ra guard cs R S scratch hyps))))))

/-- The memory of a boundary state: stack slots `stackSlots`, the first `done` fields written to the output. -/
def encodeMem (L : EncoderFrameLayout) (fields : List ContainerField) (stk : List EncodeStackSlot) (done : Nat)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8)
    (ys : List (List UInt8)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (EncodeStackSlot.chunk k s cs ys
        (fieldValues fields (bindersUint64 L.stateWord xs) (bindersContent L.stateWord fields xs)) scratch S (L.frame + 16))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ stateChunk s.regs.rax.toBitVec L.stateWord xs
      ++ encodeReceiverChunks s.regs.rax.toBitVec fields (8 * stateWords L.stateWord) (bindersUint64 L.stateWord xs) (bindersCapacity L.stateWord fields xs) ps
      ++ encodeContentChunks fields (bindersContent L.stateWord fields xs) ps
      ++ [Eq ((bindersPrefix L.stateWord fields xs).At s.regs.rbx.toBitVec)]
      ++ encodeOutputChunks (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec) fields 0 done
          (fieldValues fields (bindersUint64 L.stateWord xs) (bindersContent L.stateWord fields xs)) (bindersOverwritten L.stateWord fields xs)
      ++ [R])

/-- The fast-path post-state: `(dst, len + size, cap, nil)` and the output bytes. -/
def encodeFinalStatePredicate (L : EncoderFrameLayout) (fields : List ContainerField)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
    ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + sszSize fields ∧ st.data.regs.rcx = s.regs.rdi
    ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
    ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
    ExistsChunks L.existentials.length (fun ys => Conjunctions (existentialLengthFacts S 0 L.existentials ys)
      (encodeMem L fields L.post fields.length k xs ps s ra guard cs R S scratch ys st.data.dmem))

set_option linter.unusedVariables false in
/-- **Fast-path statement kind of a flat container encoder, any frame** (see the module text). -/
abbrev encodeFastPathKindAnyFrame (C : Program) (L : EncoderFrameLayout) (fields : List ContainerField) : Prop :=
  encodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ encodeMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat) (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (Eventually (step1 Host.exe) (encodeFinalStatePredicate L fields k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

/-- What a register holds at a field boundary: the receiver, the `dst` pointer, the capacity, `len + n`. -/
inductive EncodeRegisterValue where
  | receiver
  | ptr
  | cap
  | len (n : Nat)

def EncodeRegisterValue.val (s : MachineData) : EncodeRegisterValue → BitVec 64
  | .receiver => s.regs.rax.toBitVec
  | .ptr => s.regs.rbx.toBitVec
  | .cap => s.regs.rdi.toBitVec
  | .len n => addOffset s.regs.rcx.toBitVec n

/-- A boundary state of a generated-style fast-path proof: directive index, number of encoded fields,
register facts, stack slots, existential chunks. -/
structure EncodeBoundaryState where
  pc : Nat
  done : Nat
  regs : List (Reg64 × EncodeRegisterValue)
  stackSlots : List EncodeStackSlot
  existentials : List ExistentialLength

/-- Register facts of a boundary state. -/
def encodeRegisterFacts (s : MachineData) (st : MachineState) : List (Reg64 × EncodeRegisterValue) → List Prop
  | [] => []
  | (r, v) :: rs => (st.data.regs.get64 r = v.val s) :: encodeRegisterFacts s st rs

/-- The state predicate of a boundary state. -/
def encodeBoundaryStatePredicate (L : EncoderFrameLayout) (fields : List ContainerField) (d : EncodeBoundaryState)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 (L.frame + 8) }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    Conjunctions (encodeRegisterFacts s st d.regs)
      (ExistsChunks d.existentials.length (fun ys => Conjunctions (existentialLengthFacts S 0 d.existentials ys)
        (encodeMem L fields d.stackSlots d.done k xs ps s ra guard cs R S scratch ys st.data.dmem)))

set_option linter.unusedVariables false in
/-- Kind of the head theorem: fast-path premises, entry → boundary state `d0`. -/
abbrev encodeHeadKindAnyFrame (C : Program) (L : EncoderFrameLayout) (fields : List ContainerField) (d0 : EncodeBoundaryState) : Prop :=
  encodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ encodeMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addExtra guard.toNat L.guardAddend < s.regs.rsp.toNat) (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (Eventually (step1 Host.exe) (encodeBoundaryStatePredicate L fields d0 k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem: boundary state `d` → boundary state `d'`, under the capacity premise. -/
abbrev encodeFieldKindAnyFrame (C : Program) (L : EncoderFrameLayout) (fields : List ContainerField) (d d' : EncodeBoundaryState) : Prop :=
  encodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Implications hyps (∀ (st0 : MachineState), encodeBoundaryStatePredicate L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (encodeBoundaryStatePredicate L fields d' k xs ps s ra guard cs R S scratch) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem: boundary state `d` → the fast-path post-state. -/
abbrev encodeEpilogueKindAnyFrame (C : Program) (L : EncoderFrameLayout) (fields : List ContainerField) (d : EncodeBoundaryState) : Prop :=
  encodeBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
      (st0 : MachineState), encodeBoundaryStatePredicate L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (encodeFinalStatePredicate L fields k xs ps s ra guard cs R S scratch) st0)

end Codec
