import Codec.Kind.DecodeAcceptAnyFrame

/-!
# ENC2 L1 / L2: statement kinds for encoder fast-path theorems of flat containers, any frame

`encFastKindN C L fields` is the fast-path statement of `MarshalSSZTo` of a flat fixed-size container `C`.
**Fast path only**: premise `len(dst) + SizeSSZ ≤ cap(dst)` and every byte-vector field of its exact length.
The `runtime.growslice` branches, the length rejects and the morestack path are not part of the statement.

- `fields : List DecField` (the GEN3 type): `.bytes n` = a `[]byte` field of SSZ size `n` (receiver words:
  pointer, length `n`, capacity word); `.u64` = an 8-byte field (`uint64` or an overlay type of it).
- `L : EncLayout`: the frame facts of the `.S` file. `st` (the receiver has the protoc `state` word), `frame`
  (the `sub` amount `F`), `gd` (stack-guard addend: 0 for the small guard, `N` of `lea -N(%rsp),%r12`), `rt`
  (the function calls `runtime.memmove`: binders `S scratch`, premise `MemmoveC S`), the stack chunk binders
  and their lengths (`nstk`, `lens`), the stack slots before (`pre`) and after (`post`, `exs`).

Binder group `xs` (one list): `[ast]` (if `st`), the values of the `.u64` fields, the capacity words of the
`.bytes` fields, the contents of the `.bytes` fields, `pre` (the bytes already in `dst`), one chunk `d` per
field (the bytes of `dst[len:cap]` the field overwrites). `ps`: the pointers of the `.bytes` fields.

The receiver chunks, the content chunks, the output chunks and the sizes are computed from `fields` alone.
The stack part is a parameter: the kind does not check that `L` is the frame of the code; a proof of an
instance does (a wrong slot does not close). The premise `cap < 2 ^ 63` is kept from the hand statements.

The binder prefix (`encBinders`) is shared with the three kinds of the intermediate theorems of a
generated-style proof, stated over the WHOLE memory in entry-state terms (the GEN5 form):
- `encHeadKindN C L fields d0`: fast-path premises, entry → boundary state `d0`;
- `encFieldKindN C L fields d d'`: boundary state `d` → boundary state `d'` (one field);
- `encEpiKindN C L fields d`: boundary state `d` → the post-state.
A boundary state `EncSt` gives the directive index, the number of encoded fields, register facts and the
stack slots; `encStP` renders it. Ties to the hand statements: `Prysm/BeaconBlockHeader/EncodeFastPathKindInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- The content of a stack slot of an encoder state: an original chunk (`cs` index), the bytes of an entry
register, an existential chunk, the value of field `i`, the length `len + n`, a return address (directive
index), the scratch chunk below the `memmove` return slot. -/
inductive EVal where
  | orig (i : Nat)
  | reg (r : Reg64)
  | ex (i : Nat)
  | fld (i : Nat)
  | len (n : Nat)
  | ret (n : Nat)
  | scr

/-- A stack slot: a value at an offset from the entry rsp, or a value at `rsp - (frame + 16) - S`. -/
inductive ESlot where
  | at (o : SOff) (v : EVal)
  | lo (v : EVal)

/-- The frame facts of an encoder (see the module text). `frame` = the `sub` amount. -/
structure EncLayout where
  st : Bool
  frame : Nat
  gd : Nat
  rt : Bool
  nstk : Nat
  lens : List (Nat × Nat)
  pre : List ESlot
  exs : List ExLen
  post : List ESlot

/-- `∀ p₁ … pₘ : BitVec 64, P [p₁, …, pₘ]`. -/
def AllBV : Nat → (List (BitVec 64) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∀ p : BitVec 64, AllBV m (fun ps => P (p :: ps))

/-- Number of `.u64` fields. -/
def nU64 : List DecField → Nat
  | [] => 0
  | .u64 :: fs => nU64 fs + 1
  | .bytes _ :: fs => nU64 fs

/-- Length of the binder group `xs`. -/
def encNx (st : Bool) (fields : List DecField) : Nat :=
  stWords st + nU64 fields + 2 * nBytes fields + 1 + fields.length

/-- The parts of the binder group. -/
def xsU (st : Bool) (xs : List (List UInt8)) : List (List UInt8) := xs.drop (stWords st)
def xsCap (st : Bool) (fields : List DecField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stWords st + nU64 fields)
def xsCont (st : Bool) (fields : List DecField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stWords st + nU64 fields + nBytes fields)
def xsPre (st : Bool) (fields : List DecField) (xs : List (List UInt8)) : List UInt8 :=
  xs.getD (stWords st + nU64 fields + 2 * nBytes fields) []
def xsD (st : Bool) (fields : List DecField) (xs : List (List UInt8)) : List (List UInt8) :=
  xs.drop (stWords st + nU64 fields + 2 * nBytes fields + 1)

/-- Length hypotheses of the contents of the `.bytes` fields. -/
def contLens : List DecField → List (List UInt8) → List Prop
  | [], _ => []
  | .bytes n :: fs, bs => ((bs.headD []).length = n) :: contLens fs bs.tail
  | .u64 :: fs, bs => contLens fs bs

/-- Length hypotheses of the binder group (none for `pre`). -/
def encLens (st : Bool) (fields : List DecField) (xs : List (List UInt8)) : List Prop :=
  wordLens (stWords st + nU64 fields + nBytes fields) xs
    ++ contLens fields (xsCont st fields xs)
    ++ valLens fields (xsD st fields xs)

/-- The field values in field order (`us`: the `.u64` values, `bs`: the `.bytes` contents). -/
def fldVals : List DecField → List (List UInt8) → List (List UInt8) → List (List UInt8)
  | [], _, _ => []
  | .u64 :: fs, us, bs => us.headD [] :: fldVals fs us.tail bs
  | .bytes _ :: fs, us, bs => bs.headD [] :: fldVals fs us bs.tail

/-- The receiver words from Go offset `g`: the value of a `.u64` field; pointer, length and capacity word of
a `.bytes` field. -/
def encRcv (b : BitVec 64) : List DecField → Nat → List (List UInt8) → List (List UInt8) → List (BitVec 64)
    → List (DataMem → Prop)
  | [], _, _, _, _ => []
  | .u64 :: fs, g, us, cs, ps => Eq ((us.headD []).At (addOff b g)) :: encRcv b fs (g + 8) us.tail cs ps
  | .bytes n :: fs, g, us, cs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOff b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOff b (g + 8)))
      :: Eq ((cs.headD []).At (addOff b (g + 16)))
      :: encRcv b fs (g + 24) us cs.tail ps.tail

/-- The contents of the `.bytes` fields at their pointers. -/
def encCont : List DecField → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _ => []
  | .u64 :: fs, bs, ps => encCont fs bs ps
  | .bytes _ :: fs, bs, ps => Eq ((bs.headD []).At (ps.headD 0)) :: encCont fs bs.tail ps.tail

/-- The output chunks from SSZ offset `o`: the value of each of the first `done` fields, the old chunk `d` of
the others. -/
def encOut (b : BitVec 64) : List DecField → Nat → Nat → List (List UInt8) → List (List UInt8)
    → List (DataMem → Prop)
  | [], _, _, _, _ => []
  | f :: fs, o, 0, vals, ds => Eq ((ds.headD []).At (addOff b o)) :: encOut b fs (o + f.size) 0 vals.tail ds.tail
  | f :: fs, o, d + 1, vals, ds =>
    Eq ((vals.headD []).At (addOff b o)) :: encOut b fs (o + f.size) d vals.tail ds.tail

variable [Host]

/-- The bytes of a slot value. -/
def EVal.bytes (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8) :
    EVal → List UInt8
  | .orig i => cs.getD i []
  | .reg r => Int.toBytes 8 (s.regs.get64 r).toInt
  | .ex i => ys.getD i []
  | .fld i => vals.getD i []
  | .len n => Int.toBytes 8 (s.regs.rcx.toBitVec + BitVec.ofNat 64 n).toInt
  | .ret n => Int.toBytes 8 (Host.addrOf (k + n)).toBitVec.toInt
  | .scr => scratch

/-- The memory chunk of a stack slot. -/
def ESlot.chunk (k : Nat) (s : MachineData) (cs ys vals : List (List UInt8)) (scratch : List UInt8)
    (S loB : Nat) : ESlot → DataMem → Prop
  | .at o v => Eq ((v.bytes k s cs ys vals scratch).At (o.addr s.regs.rsp.toBitVec))
  | .lo v => Eq ((v.bytes k s cs ys vals scratch).At
      (s.regs.rsp.toBitVec - BitVec.ofNat 64 loB - BitVec.ofNat 64 S))

/-- The `memmove` binders: nothing, or `S`, `scratch`, `hsc`; the body gets the hypothesis `MemmoveC S`. -/
def encRt (rt : Bool) (body : Nat → List UInt8 → List Prop → Prop) : Prop :=
  match rt with
  | false => body 0 [] []
  | true => ∀ (S : Nat) (scratch : List UInt8), scratch.length = S → body S scratch [MemmoveC S]

set_option linter.unusedVariables false in
/-- The binder prefix of every ENC2 kind: code placement, the binder group and its lengths, the field
pointers, the entry state, `hpre`, the stack chunks and their lengths, the frame `R`, the `memmove` binders. -/
def encBinders (C : Program) (L : EncLayout) (fields : List DecField)
    (body : Nat → List (List UInt8) → List (BitVec 64) → MachineData → UInt64 → UInt64 → List (List UInt8)
      → (DataMem → Prop) → Nat → List UInt8 → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllL (encNx L.st fields) (fun xs => Imps (encLens L.st fields xs)
    (AllBV (nBytes fields) (fun ps => ∀ (s : MachineData) (ra guard : UInt64),
      (xsPre L.st fields xs).length = s.regs.rcx.toNat →
      AllL L.nstk (fun cs => Imps (csLens L.lens cs)
        (∀ (R : DataMem → Prop), encRt L.rt (fun S scratch hyps =>
          body k xs ps s ra guard cs R S scratch hyps))))))

/-- The memory of a boundary state: stack slots `stk`, the first `done` fields written to the output. -/
def encMem (L : EncLayout) (fields : List DecField) (stk : List ESlot) (done : Nat)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8)
    (ys : List (List UInt8)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (ESlot.chunk k s cs ys
        (fldVals fields (xsU L.st xs) (xsCont L.st fields xs)) scratch S (L.frame + 16))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ stChunk s.regs.rax.toBitVec L.st xs
      ++ encRcv s.regs.rax.toBitVec fields (8 * stWords L.st) (xsU L.st xs) (xsCap L.st fields xs) ps
      ++ encCont fields (xsCont L.st fields xs) ps
      ++ [Eq ((xsPre L.st fields xs).At s.regs.rbx.toBitVec)]
      ++ encOut (s.regs.rbx.toBitVec + s.regs.rcx.toBitVec) fields 0 done
          (fldVals fields (xsU L.st xs) (xsCont L.st fields xs)) (xsD L.st fields xs)
      ++ [R])

/-- The fast-path post-state: `(dst, len + size, cap, nil)` and the output bytes. -/
def encFinalP (L : EncLayout) (fields : List DecField)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
    ∧ st.data.regs.rbx.toNat = s.regs.rcx.toNat + sszSize fields ∧ st.data.regs.rcx = s.regs.rdi
    ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
    ∧ st.data.regs.rsp = s.regs.rsp + 8 ∧ st.data.regs.rbp = s.regs.rbp ∧ st.data.regs.r14 = s.regs.r14 ∧
    ExCh L.exs.length (fun ys => AndL (exLens S 0 L.exs ys)
      (encMem L fields L.post fields.length k xs ps s ra guard cs R S scratch ys st.data.dmem))

set_option linter.unusedVariables false in
/-- **Fast-path statement kind of a flat container encoder, any frame** (see the module text). -/
abbrev encFastKindN (C : Program) (L : EncLayout) (fields : List DecField) : Prop :=
  encBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ encMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addX guard.toNat L.gd < s.regs.rsp.toNat) (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Imps hyps (Eventually (step1 Host.exe) (encFinalP L fields k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

/-- What a register holds at a field boundary: the receiver, the `dst` pointer, the capacity, `len + n`. -/
inductive ERV where
  | rcv
  | ptr
  | cap
  | len (n : Nat)

def ERV.val (s : MachineData) : ERV → BitVec 64
  | .rcv => s.regs.rax.toBitVec
  | .ptr => s.regs.rbx.toBitVec
  | .cap => s.regs.rdi.toBitVec
  | .len n => addOff s.regs.rcx.toBitVec n

/-- A boundary state of a generated-style fast-path proof: directive index, number of encoded fields,
register facts, stack slots, existential chunks. -/
structure EncSt where
  pc : Nat
  done : Nat
  regs : List (Reg64 × ERV)
  stk : List ESlot
  exs : List ExLen

/-- Register facts of a boundary state. -/
def eregFacts (s : MachineData) (st : MachineState) : List (Reg64 × ERV) → List Prop
  | [] => []
  | (r, v) :: rs => (st.data.regs.get64 r = v.val s) :: eregFacts s st rs

/-- The state predicate of a boundary state. -/
def encStP (L : EncLayout) (fields : List DecField) (d : EncSt)
    (k : Nat) (xs : List (List UInt8)) (ps : List (BitVec 64)) (s : MachineData) (ra guard : UInt64)
    (cs : List (List UInt8)) (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) : MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 (L.frame + 8) }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    AndL (eregFacts s st d.regs)
      (ExCh d.exs.length (fun ys => AndL (exLens S 0 d.exs ys)
        (encMem L fields d.stk d.done k xs ps s ra guard cs R S scratch ys st.data.dmem)))

set_option linter.unusedVariables false in
/-- Kind of the head theorem: fast-path premises, entry → boundary state `d0`. -/
abbrev encHeadKindN (C : Program) (L : EncLayout) (fields : List DecField) (d0 : EncSt) : Prop :=
  encBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (h_mem : s.dmem =⋆ encMem L fields L.pre 0 k xs ps s ra guard cs R S scratch [])
      (hguard : addX guard.toNat L.gd < s.regs.rsp.toNat) (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Imps hyps (Eventually (step1 Host.exe) (encStP L fields d0 k xs ps s ra guard cs R S scratch)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem: boundary state `d` → boundary state `d'`, under the capacity premise. -/
abbrev encFieldKindN (C : Program) (L : EncLayout) (fields : List DecField) (d d' : EncSt) : Prop :=
  encBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63),
      Imps hyps (∀ (st0 : MachineState), encStP L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (encStP L fields d' k xs ps s ra guard cs R S scratch) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem: boundary state `d` → the fast-path post-state. -/
abbrev encEpiKindN (C : Program) (L : EncLayout) (fields : List DecField) (d : EncSt) : Prop :=
  encBinders C L fields (fun k xs ps s ra guard cs R S scratch hyps =>
    ∀ (hsp : L.frame + 16 ≤ s.regs.rsp.toNat)
      (hcap : s.regs.rcx.toNat + sszSize fields ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63)
      (st0 : MachineState), encStP L fields d k xs ps s ra guard cs R S scratch st0 →
        Eventually (step1 Host.exe) (encFinalP L fields k xs ps s ra guard cs R S scratch) st0)

end Codec
