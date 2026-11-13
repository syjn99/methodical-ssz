import Prysm.BlobIdentifier.DecodeAccept
import Prysm.DepositMessage.DecodeAccept
import Prysm.Eth1Data.DecodeAccept
import Prysm.Deposit_Data.Statements

/-!
# GEN3 L4: a statement kind for composed decoder accept theorems (byte-vector / inline-uint64 shapes)

`decAcceptKind C st fields jret` is the accept statement of a protoc container decoder `C` whose fields are
fixed byte vectors (`DecField.bytes n`: a fresh `n`-byte slice, `len = cap = n`) and inline `uint64`s
(`DecField.u64`), in the frame of the development decoders (`sub $0x20`; `Codec/DecoderHeadEpilogue.lean`). `st` says that the
receiver has one word before the first field (the protoc `state`); `jret` is the directive whose address
is in the runtime-call return slot at the end (the directive after the last `callq runtime.memmove`).
The statement is computed by structural recursion on `fields`: the SSZ offsets are the running sum of the
field sizes, the Go offsets the running sum of 24 (slice header) / 8 from 8 (`st`) or 0, the input size and
the heap use are sums. Binders of the hand statements are list elements here (`AllL`, `ExBV`), their length
hypotheses an implication chain (`Imps`), the memory a left fold of `⋆` (`sepAll`).

Tie to the existing theorems (`rfl` at default transparency; the recursive definitions unfold on the literal
field list): the declared types of `Prysm.BlobIdentifier.Decode.accept`, `Prysm.DepositMessage.Decode.accept`, `Prysm.Eth1Data.Decode.accept`
(these are the declared types of the three generated composed theorems `*_accept_main_gc`, by their `_type`
lines) and the hand statement `Prysm.Deposit_Data.Decode.accept_statement`. So a composed theorem of this shape can be
statement-checked against `decAcceptKind` with parameters read from the IR, without a hand theorem.
Not covered: callee-decoder fields, other frames, a first field that is not at Go offset 0 or 8.
After the split of this module, the declarations of single types are in `Prysm/BlobIdentifier/DecodeAcceptComposition.lean`, `Prysm/DepositMessage/DecodeAcceptComposition.lean`, `Prysm/Deposit_Data/DecodeAcceptComposition.lean`, `Prysm/Eth1Data/DecodeAcceptComposition.lean`.
-/

open Machine Runtime

open Codec
namespace Codec

/-- A field of a composed decoder: a fixed byte vector of `n` bytes, or an inline `uint64`. -/
inductive DecField where
  | bytes (n : Nat)
  | u64

namespace DecField

/-- SSZ size. -/
def size : DecField → Nat
  | bytes n => n
  | u64 => 8

/-- Heap bytes used by the decoder for the field. -/
def heap : DecField → Nat
  | bytes n => n
  | u64 => 0

/-- Number of 8-byte receiver words. -/
def words : DecField → Nat
  | bytes _ => 3
  | u64 => 1

end DecField

/-- `∀ x₁ … xₘ : List UInt8, P [x₁, …, xₘ]`. -/
def AllL : Nat → (List (List UInt8) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∀ x : List UInt8, AllL m (fun xs => P (x :: xs))

/-- `∃ p₁ … pₘ : BitVec 64, P [p₁, …, pₘ]`. -/
def ExBV : Nat → (List (BitVec 64) → Prop) → Prop
  | 0, P => P []
  | m + 1, P => ∃ p : BitVec 64, ExBV m (fun ps => P (p :: ps))

/-- `A₁ → … → Aₘ → Q`. -/
def Imps : List Prop → Prop → Prop
  | [], Q => Q
  | A :: As, Q => A → Imps As Q

/-- `b` for offset 0, else `b + o`. -/
def addOff (b : BitVec 64) : Nat → BitVec 64
  | 0 => b
  | o + 1 => b + BitVec.ofNat 64 (o + 1)

/-- `init ⋆ p₁ ⋆ … ⋆ pₘ` (left-nested, as the notation). -/
def sepAll (init : DataMem → Prop) (ps : List (DataMem → Prop)) : DataMem → Prop :=
  ps.foldl (fun a b => a ⋆ b) init

def sszSize (fs : List DecField) : Nat := fs.foldl (fun a f => a + f.size) 0
def heapSize (fs : List DecField) : Nat := fs.foldl (fun a f => a + f.heap) 0
def rcvWords (fs : List DecField) : Nat := fs.foldl (fun a f => a + f.words) 0
def nBytes : List DecField → Nat
  | [] => 0
  | .bytes _ :: fs => nBytes fs + 1
  | .u64 :: fs => nBytes fs

/-- Length hypotheses of the field values. -/
def valLens : List DecField → List (List UInt8) → List Prop
  | [], _ => []
  | f :: fs, vs => ((vs.headD []).length = f.size) :: valLens fs vs.tail

/-- `c` hypotheses "length = 8". -/
def wordLens : Nat → List (List UInt8) → List Prop
  | 0, _ => []
  | c + 1, cs => ((cs.headD []).length = 8) :: wordLens c cs.tail

/-- The input chunks: field value `i` at its SSZ offset from `b`. -/
def inChunks (b : BitVec 64) : List DecField → Nat → List (List UInt8) → List (DataMem → Prop)
  | [], _, _ => []
  | f :: fs, o, vs => Eq ((vs.headD []).At (addOff b o)) :: inChunks b fs (o + f.size) vs.tail

/-- The receiver words before the call: one arbitrary 8-byte chunk per word, from Go offset `g`. -/
def rcvPre (b : BitVec 64) : Nat → Nat → List (List UInt8) → List (DataMem → Prop)
  | 0, _, _ => []
  | c + 1, g, cs => Eq ((cs.headD []).At (addOff b g)) :: rcvPre b c (g + 8) cs.tail

/-- The receiver words after the call: slice header (pointer, len, cap) or the 8 value bytes. -/
def rcvPost (b : BitVec 64) : List DecField → Nat → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _, _ => []
  | .bytes n :: fs, g, vs, ps =>
    Eq ((Int.toBytes 8 (ps.headD 0).toInt).At (addOff b g))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOff b (g + 8)))
      :: Eq ((Int.toBytes 8 (Int.ofNat n)).At (addOff b (g + 16)))
      :: rcvPost b fs (g + 24) vs.tail ps.tail
  | .u64 :: fs, g, vs, ps => Eq ((vs.headD []).At (addOff b g)) :: rcvPost b fs (g + 8) vs.tail ps

/-- The new heap chunks: the bytes of each byte-vector field at its pointer. -/
def heapPost : List DecField → List (List UInt8) → List (BitVec 64) → List (DataMem → Prop)
  | [], _, _ => []
  | .bytes _ :: fs, vs, ps => Eq ((vs.headD []).At (ps.headD 0)) :: heapPost fs vs.tail ps.tail
  | .u64 :: fs, vs, ps => heapPost fs vs.tail ps

/-- 1 if the receiver has a `state` word before the first field. -/
def stWords : Bool → Nat
  | true => 1
  | false => 0

/-- The `state` chunk (if any). -/
def stChunk (b : BitVec 64) : Bool → List (List UInt8) → List (DataMem → Prop)
  | true, cs => [Eq ((cs.headD []).At b)]
  | false, _ => []

variable [Host]

set_option linter.unusedVariables false in
/-- Accept statement kind of a composed container decoder (see the module text). Stack chunk list `cs`:
`fp s1 s2 spl l18 rslot lo`, then `ast` (if `st`), then the receiver words. -/
abbrev decAcceptKind (C : Program) (st : Bool) (fields : List DecField) (jret : Nat) : Prop :=
  ∀ (k : Nat) (hk : C.IsInfixAt Host.prog k) (hf : LabelsFresh C k),
  AllL fields.length (fun vs => Imps (valLens fields vs)
    (∀ (s : MachineData) (ra guard : UInt64),
    AllL (7 + stWords st + rcvWords fields) (fun cs =>
      Imps ([(cs.getD 0 []).length = 8, (cs.getD 1 []).length = 8, (cs.getD 2 []).length = 8,
          (cs.getD 3 []).length = 24, (cs.getD 4 []).length = 8, (cs.getD 5 []).length = 8]
        ++ wordLens (stWords st + rcvWords fields) (cs.drop 7))
      (∀ (R : DataMem → Prop) (S : Nat) (hlo : (cs.getD 6 []).length = S)
        (Heap : Nat → DataMem → Prop) (avail : Nat)
        (h_mem : s.dmem =⋆ sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
          ([Eq ((cs.getD 0 []).At (s.regs.rsp.toBitVec - 8)), Eq ((cs.getD 1 []).At (s.regs.rsp.toBitVec + 8)),
            Eq ((cs.getD 2 []).At (s.regs.rsp.toBitVec + 16)),
            Eq ((cs.getD 3 []).At (s.regs.rsp.toBitVec - 40)), Eq ((cs.getD 4 []).At (s.regs.rsp.toBitVec - 16)),
            Eq ((cs.getD 5 []).At (s.regs.rsp.toBitVec - 48)),
            Eq ((cs.getD 6 []).At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S)),
            Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)),
            Heap avail]
          ++ inChunks s.regs.rbx.toBitVec fields 0 vs
          ++ stChunk s.regs.rax.toBitVec st (cs.drop 7)
          ++ rcvPre s.regs.rax.toBitVec (rcvWords fields) (8 * stWords st) (cs.drop (7 + stWords st))
          ++ [Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec), R]))
        (hguard : guard.toNat < s.regs.rsp.toNat) (hlen : s.regs.rcx = UInt64.ofNat (sszSize fields))
        (hav : heapSize fields ≤ avail)
        (hms : MakesliceC Heap ElfData.CheckpointAndEpoch.e2eU8Type_addr 1 S) (hmm : MemmoveC S),
        Eventually (step1 Host.exe)
          (fun st' => st'.pc = Int64.ofBitVec ra.toBitVec ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
            ∧ st'.data.regs.rsp = s.regs.rsp + 8 ∧ st'.data.regs.rbp = s.regs.rbp
            ∧ st'.data.regs.r14 = s.regs.r14 ∧
            ExBV (nBytes fields) (fun ps => ∃ (spl' lo' : List UInt8), spl'.length = 24 ∧ lo'.length = S ∧
              (sepAll (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec))
                ([Eq ((Int.toBytes 8 s.regs.rbp.toBitVec.toInt).At (s.regs.rsp.toBitVec - 8)),
                  Eq ((Int.toBytes 8 s.regs.rax.toBitVec.toInt).At (s.regs.rsp.toBitVec + 8)),
                  Eq ((Int.toBytes 8 s.regs.rbx.toBitVec.toInt).At (s.regs.rsp.toBitVec + 16)),
                  Eq (spl'.At (s.regs.rsp.toBitVec - 40)),
                  Eq ((Int.toBytes 8 (ps.getLastD 0).toInt).At (s.regs.rsp.toBitVec - 16)),
                  Eq ((Int.toBytes 8 (Host.addrOf (k + jret)).toBitVec.toInt).At (s.regs.rsp.toBitVec - 48)),
                  Eq (lo'.At (s.regs.rsp.toBitVec - 48 - BitVec.ofNat 64 S)),
                  Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16)),
                  Heap (avail - heapSize fields)]
                ++ inChunks s.regs.rbx.toBitVec fields 0 vs
                ++ stChunk s.regs.rax.toBitVec st (cs.drop 7)
                ++ rcvPost s.regs.rax.toBitVec fields (8 * stWords st) vs ps
                ++ heapPost fields vs ps
                ++ [Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec), R])) st'.data.dmem))
          ⟨s, Host.addrOf k⟩))))

end Codec
