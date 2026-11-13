import Codec.Kind.DecodeAcceptComposition

/-!
# GEN5 L1 / L2: statement kinds for whole accept theorems of flat decoders, any frame

`decAcceptKindN C L fields` is the accept statement of a flat fixed-size container decoder `C`.
- `fields : List DecField` (the GEN3 type): fixed byte vectors (`.bytes n`, a fresh slice, `len = cap = n`) and
  8-byte fields (`.u64`). A field decoded by a callee (`Slot`, `Epoch`, `ValidatorIndex`, `CommitteeIndex`
  `UnmarshalSSZ`) is `.u64` here: in the receiver and in the input it is the same as an inline `uint64`. The
  callee shows only as placement premises (`L.callees`).
- `L : DecLayout`: the frame facts of the `.S` file. Stack chunk binders and length hypotheses (`nstk`,
  `lens`), the stack slots before (`pre`) and after (`post`, `exs`), the runtime configuration (`rt`: `none`
  for a decoder without `makeslice` / `memmove`), the stack-guard addend (`gd`), the `state` word (`st`).

The input chunks, the receiver words before and after, the heap chunks and the sizes are computed from
`fields` by the GEN3 functions of `Codec/Kind/DecodeAcceptComposition.lean` (unchanged). The stack part is a parameter: the kind does
not check that `L` is the frame of the code; a proof of an instance does (a wrong slot does not close).
The kind does not check that `L.callees` are the callees of the fields: that is a rule of the generator.

The binder prefix (`decBinders`) is shared with the three kinds of the intermediate theorems of a generated
accept proof (GEN5 L2). These are stated over the WHOLE accept memory in entry-state terms:
- `decHeadKindN C L fields d0`: accept premises, entry → boundary state `d0`;
- `decFieldKindN C L fields d d'`: boundary state `d` → boundary state `d'` (one field);
- `decEpiKindN C L fields d`: boundary state `d` → the accept post-state.
A boundary state `StDesc` gives the directive index, the number of decoded fields, register facts and the
stack slots; `decStP` renders it. The accept proof chains the theorems with `eventually_trans` only.

Ties to the hand statements: `Codec/Kind/DecodeAcceptAnyFrameInstances.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- A stack offset from the entry rsp: `rsp + n` or `rsp - n`. -/
inductive SOff where
  | up (n : Nat)
  | dn (n : Nat)

/-- The address of a stack offset. -/
def SOff.addr (b : BitVec 64) : SOff → BitVec 64
  | .up n => b + BitVec.ofNat 64 n
  | .dn n => b - BitVec.ofNat 64 n

/-- The content of a stack slot: an original chunk (`cs` index), the bytes of an entry register, an
existential chunk, the pointer of a byte field (index among the byte fields), zero, or a return address
(directive index). -/
inductive SVal where
  | orig (i : Nat)
  | reg (r : Reg64)
  | ex (i : Nat)
  | ptr (i : Nat)
  | zero
  | ret (n : Nat)

/-- A stack slot: a value at an offset, or a value at the low-stack address `rsp - loB - S`. -/
inductive SSlot where
  | at (o : SOff) (v : SVal)
  | lo (v : SVal)

/-- Length of an existential chunk: a number, or the low-stack length. -/
inductive ExLen where
  | n (len : Nat)
  | lo

/-- Runtime configuration of a decoder with `makeslice` / `memmove` calls: premise `S < 2 ^ 60` (`hS`), the
low-stack chunk has `S + x` bytes (`x = 0`: `S`), its index among the stack chunks, its address
`rsp - loB - S`. -/
structure RtCfg where
  hS : Bool
  x : Nat
  loIdx : Nat
  loB : Nat

/-- The frame facts of a decoder (see the module text). `frame` = entry rsp − rsp inside the body. -/
structure DecLayout where
  callees : List Program
  nstk : Nat
  lens : List (Nat × Nat)
  pre : List SSlot
  rt : Option RtCfg
  gd : Nat
  st : Bool
  exs : List ExLen
  post : List SSlot
  frame : Nat

/-- `a` for 0, else `a + x`. -/
def addX (a : Nat) : Nat → Nat
  | 0 => a
  | x + 1 => a + (x + 1)

/-- `∃ x₁ … xₘ : List UInt8, P [x₁, …, xₘ]`. -/
def ExCh : Nat → (List (List UInt8) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∃ x : List UInt8, ExCh m (fun xs => P (x :: xs))

/-- `A₁ ∧ … ∧ Aₘ ∧ Q`. -/
def AndL : List Prop → Prop → Prop
  | [], Q => Q
  | A :: As, Q => A ∧ AndL As Q

/-- Length hypotheses `(cs[i]).length = l` of the stack chunks. -/
def csLens : List (Nat × Nat) → List (List UInt8) → List Prop
  | [], _ => []
  | (i, l) :: r, cs => ((cs.getD i []).length = l) :: csLens r cs

/-- `[S < 2 ^ 60]` or nothing. -/
def sLt : Bool → Nat → List Prop
  | true, S => [S < 2 ^ 60]
  | false, _ => []

def ExLen.len (S x : Nat) : ExLen → Nat
  | .n l => l
  | .lo => addX S x

/-- Length facts of the existential chunks. -/
def exLens (S x : Nat) : List ExLen → List (List UInt8) → List Prop
  | [], _ => []
  | e :: es, xs => ((xs.headD []).length = e.len S x) :: exLens S x es xs.tail

def RtCfg.xOf : Option RtCfg → Nat
  | none => 0
  | some c => c.x

def RtCfg.loBOf : Option RtCfg → Nat
  | none => 0
  | some c => c.loB

variable [Host]

/-- `∀ (kP : Nat) (hkP : P.IsInfixAt Host.prog kP) (hfP : LabelsFresh P kP), …` for every callee program. -/
def AllPlaced : List Program → Prop → Prop
  | [], Q => Q
  | P :: Ps, Q => ∀ (kP : Nat) (_ : P.IsInfixAt Host.prog kP) (_ : LabelsFresh P kP), AllPlaced Ps Q

/-- The bytes of a slot value. -/
def SVal.bytes (k : Nat) (s : MachineData) (cs xs : List (List UInt8)) (ps : List (BitVec 64)) : SVal → List UInt8
  | .orig i => cs.getD i []
  | .reg r => Int.toBytes 8 (s.regs.get64 r).toInt
  | .ex i => xs.getD i []
  | .ptr i => Int.toBytes 8 (ps.getD i 0).toInt
  | .zero => Int.toBytes 8 (0 : UInt64).toBitVec.toInt
  | .ret n => Int.toBytes 8 (Host.addrOf (k + n)).toBitVec.toInt

/-- The memory chunk of a stack slot. -/
def SSlot.chunk (k : Nat) (s : MachineData) (cs xs : List (List UInt8)) (ps : List (BitVec 64)) (S loB : Nat) :
    SSlot → DataMem → Prop
  | .at o v => Eq ((v.bytes k s cs xs ps).At (o.addr s.regs.rsp.toBitVec))
  | .lo v => Eq ((v.bytes k s cs xs ps).At (s.regs.rsp.toBitVec - BitVec.ofNat 64 loB - BitVec.ofNat 64 S))

/-- The runtime binders: nothing (`none`), or `S`, `hS`, `hlo`, `Heap`, `avail`. The body gets `S`, the heap
chunk after `h` used bytes, the `writeBarrier` chunk and the hypotheses `hav hms hmm`. -/
def rtBind (rt : Option RtCfg) (hsz : Nat) (cs : List (List UInt8))
    (body : Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  match rt with
  | none => body 0 (fun _ => []) [] []
  | some c => ∀ (S : Nat), Imps (sLt c.hS S) ((cs.getD c.loIdx []).length = addX S c.x →
      ∀ (Heap : Nat → DataMem → Prop) (avail : Nat),
        body S (fun h => [Heap (avail - h)]) [Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)]
          [hsz ≤ avail, MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 (addX S c.x), MemmoveC (addX S c.x)])

set_option linter.unusedVariables false in
/-- The binder prefix of every GEN5 kind: code placement, callee placements, field values and their lengths,
entry state, stack and receiver chunks and their lengths, the frame `R`, the runtime binders. -/
def decBinders (C : Program) (L : DecLayout) (fields : List DecField)
    (body : Nat → List (List UInt8) → MachineData → UInt64 → UInt64 → List (List UInt8) → (DataMem → Prop)
      → Nat → (Nat → List (DataMem → Prop)) → List (DataMem → Prop) → List Prop → Prop) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllPlaced L.callees
  (AllL fields.length (fun vs => Imps (valLens fields vs)
    (∀ (s : MachineData) (ra guard : UInt64),
    AllL (L.nstk + stWords L.st + rcvWords fields) (fun cs =>
      Imps (csLens L.lens cs ++ wordLens (stWords L.st + rcvWords fields) (cs.drop L.nstk))
      (∀ (R : DataMem → Prop), rtBind L.rt (heapSize fields) cs (fun S heapAt wb hyps =>
        body k vs s ra guard cs R S heapAt wb hyps))))))

/-- The memory of a boundary state: stack slots `stk`, the first `done` fields decoded. -/
def decMem (L : DecLayout) (fields : List DecField) (stk : List SSlot) (done : Nat)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop))
    (xs : List (List UInt8)) (ps : List (BitVec 64)) : DataMem → Prop :=
  sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
    (stk.map (SSlot.chunk k s cs xs ps S (RtCfg.loBOf L.rt))
      ++ [Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))]
      ++ heapAt (heapSize (fields.take done))
      ++ inChunks s.regs.rbx.toBitVec fields 0 vs
      ++ stChunk s.regs.rax.toBitVec L.st (cs.drop L.nstk)
      ++ rcvPost s.regs.rax.toBitVec (fields.take done) (8 * stWords L.st) vs ps
      ++ rcvPre s.regs.rax.toBitVec (rcvWords (fields.drop done))
          (8 * stWords L.st + 8 * rcvWords (fields.take done))
          (cs.drop (L.nstk + stWords L.st + rcvWords (fields.take done)))
      ++ heapPost (fields.take done) vs ps
      ++ wb ++ [R])

/-- The accept post-state. -/
def decFinalP (L : DecLayout) (fields : List DecField)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st' => st'.pc = Int64.ofBitVec ra.toBitVec ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
    ∧ st'.data.regs.rsp = s.regs.rsp + 8 ∧ st'.data.regs.rbp = s.regs.rbp
    ∧ st'.data.regs.r14 = s.regs.r14 ∧
    ExBV (nBytes fields) (fun ps => ExCh L.exs.length (fun xs => AndL (exLens S (RtCfg.xOf L.rt) L.exs xs)
      (decMem L fields L.post fields.length k vs s ra guard cs R S heapAt wb xs ps st'.data.dmem)))

set_option linter.unusedVariables false in
/-- **Accept statement kind of a flat container decoder, any frame** (see the module text). -/
abbrev decAcceptKindN (C : Program) (L : DecLayout) (fields : List DecField) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ decMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addX guard.toNat L.gd < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize fields)),
      Imps hyps (Eventually (step1 Host.exe) (decFinalP L fields k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

/-- What a register holds at a field boundary: the receiver, the buffer, or zero. -/
inductive RV where
  | rcv
  | bf
  | zero

def RV.val (s : MachineData) : RV → BitVec 64
  | .rcv => s.regs.rax.toBitVec
  | .bf => s.regs.rbx.toBitVec
  | .zero => 0

/-- A boundary state of a generated accept proof: directive index, number of decoded fields, register facts,
stack slots, existential chunks. -/
structure StDesc where
  pc : Nat
  done : Nat
  regs : List (Reg64 × RV)
  stk : List SSlot
  exs : List ExLen

/-- Register facts of a boundary state. -/
def regFacts (s : MachineData) (st : MachineState) : List (Reg64 × RV) → List Prop
  | [] => []
  | (r, v) :: rs => (st.data.regs.get64 r = v.val s) :: regFacts s st rs

/-- The state predicate of a boundary state. -/
def decStP (L : DecLayout) (fields : List DecField) (d : StDesc)
    (k : Nat) (vs : List (List UInt8)) (s : MachineData) (ra guard : UInt64) (cs : List (List UInt8))
    (R : DataMem → Prop) (S : Nat) (heapAt : Nat → List (DataMem → Prop)) (wb : List (DataMem → Prop)) :
    MachineState → Prop :=
  fun st => st.pc = Host.addrOf (k + d.pc)
    ∧ st.data.regs.rsp = { toBitVec := s.regs.rsp.toBitVec - BitVec.ofNat 64 L.frame }
    ∧ st.data.regs.rbp = { toBitVec := s.regs.rsp.toBitVec - 8 } ∧ st.data.regs.r14 = s.regs.r14 ∧
    AndL (regFacts s st d.regs)
      (ExBV (nBytes (fields.take d.done)) (fun ps => ExCh d.exs.length (fun xs =>
        AndL (exLens S (RtCfg.xOf L.rt) d.exs xs)
          (decMem L fields d.stk d.done k vs s ra guard cs R S heapAt wb xs ps st.data.dmem))))

set_option linter.unusedVariables false in
/-- Kind of the head theorem of a generated accept proof: accept premises, entry → boundary state `d0`. -/
abbrev decHeadKindN (C : Program) (L : DecLayout) (fields : List DecField) (d0 : StDesc) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (h_mem : s.dmem =⋆ decMem L fields L.pre 0 k vs s ra guard cs R S heapAt wb [] [])
      (hguard : addX guard.toNat L.gd < s.regs.rsp.toNat)
      (hlen : s.regs.rcx = UInt64.ofNat (sszSize fields)),
      Imps hyps (Eventually (step1 Host.exe) (decStP L fields d0 k vs s ra guard cs R S heapAt wb)
        ⟨s, Host.addrOf k⟩))

set_option linter.unusedVariables false in
/-- Kind of a field theorem of a generated accept proof: boundary state `d` → boundary state `d'`. -/
abbrev decFieldKindN (C : Program) (L : DecLayout) (fields : List DecField) (d d' : StDesc) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (hguard : addX guard.toNat L.gd < s.regs.rsp.toNat),
      Imps hyps (∀ (st0 : MachineState), decStP L fields d k vs s ra guard cs R S heapAt wb st0 →
        Eventually (step1 Host.exe) (decStP L fields d' k vs s ra guard cs R S heapAt wb) st0))

set_option linter.unusedVariables false in
/-- Kind of the epilogue theorem of a generated accept proof: boundary state `d` → the accept post-state. -/
abbrev decEpiKindN (C : Program) (L : DecLayout) (fields : List DecField) (d : StDesc) : Prop :=
  decBinders C L fields (fun k vs s ra guard cs R S heapAt wb hyps =>
    ∀ (st0 : MachineState), decStP L fields d k vs s ra guard cs R S heapAt wb st0 →
      Eventually (step1 Host.exe) (decFinalP L fields k vs s ra guard cs R S heapAt wb) st0)

end Codec
