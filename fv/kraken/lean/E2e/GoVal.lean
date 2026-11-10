import E2e.Layout
import E2e.WitCpA
import E2e.WitCpM
import E2e.WitCpMR

/-!
# Go-value element (prysm-e2e, INBOX 004 item 5)

`cp_layout`: the offsets that the machine theorems use for the receiver (state 0,
Epoch 8, Root 16/24/32, unknownFields 40, sizeCache 64, size 72) are the
generated layout `E2e.cpGoFields` (from `prysm/ir/ir-mainnet.json`, go/types gc
amd64; TRUST: not read from the ELF's abi.Type, which has no named symbol).

`cpGoValue b`: the 72 bytes `b` are a Go value of `v1alpha1.Checkpoint`: length
72; the two slice headers (`Root`, `unknownFields`) have `len ≤ cap < 2^63` and
a nil pointer only with `cap = 0`. (`state` is a pointer field: any word;
`sizeCache` is an int32: any 4 bytes; the 4 padding bytes are not constrained.)
The theorems below check, by evaluation, that the receiver bytes inside every
witness memory block are such Go values: before the decoder (a zero
`&Checkpoint{}`), after it (`Root` = (heap block, 32, 32)), and in the encoder
witnesses.
-/

namespace E2e

def cpOff (f : String) : Nat := ((cpGoFields.find? (·.1 = f)).map (·.2.1)).getD 0

theorem cp_layout : cpOff "state" = 0 ∧ cpOff "Epoch" = 8 ∧ cpOff "Root" = 16 ∧ cpOff "unknownFields" = 40
    ∧ cpOff "sizeCache" = 64 ∧ cpGoSize = 72 := by decide

/-- Little-endian unsigned value of a byte list. -/
def u64le (l : List UInt8) : Nat := l.foldr (fun x acc => x.toNat + 256 * acc) 0

def word (b : List UInt8) (o : Nat) : Nat := u64le ((b.drop o).take 8)

/-- A Go slice header at offset `o`: `len ≤ cap < 2^63`, nil pointer only with `cap = 0`. -/
def goSliceOk (b : List UInt8) (o : Nat) : Bool :=
  decide (word b (o + 8) ≤ word b (o + 16)) && decide (word b (o + 16) < 2 ^ 63)
    && (word b o != 0 || word b (o + 16) == 0)

def cpGoValue (b : List UInt8) : Bool :=
  decide (b.length = cpGoSize) && goSliceOk b (cpOff "Root") && goSliceOk b (cpOff "unknownFields")

/-- The receiver bytes at offset `o` of a witness block. -/
def recvAt (blk : List UInt8) (o : Nat) : List UInt8 := (blk.drop o).take cpGoSize

open WitCpA in
/-- Decoder witness, before the call: the receiver (offset 0x5c of the block) is a zero `Checkpoint`. -/
theorem witCpA_recv_pre : cpGoValue (recvAt (WitCpA.block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)) 0x5c)
    = true := by decide

/-- Decoder witness, after the call: Epoch = the input, Root = (heap block 0x1000c, 32, 32). -/
theorem witCpA_recv_post :
    cpGoValue (List.replicate 8 0 ++ Int.toBytes 8 0x0123456789abcdef ++ Int.toBytes 8 (0x1000c : BitVec 64).toInt
      ++ Int.toBytes 8 32 ++ Int.toBytes 8 32 ++ List.replicate 32 0) = true := by decide

open WitCpM in
/-- Encoder witnesses: the receiver at offset 8 (Root = (0x10050, 32, 32)). -/
theorem witCpM_recv : cpGoValue (recvAt (WitCpM.block (Int.toBytes 8 0x0123456789abcdef) (List.replicate 32 0xff)
    [] []) 8) = true := by decide

open WitCpMR in
/-- Encoder reject witness: the receiver at offset 24 with `len(Root)` 31, 33, 0 and cap 48. -/
theorem witCpMR_recv : cpGoValue (recvAt (WitCpMR.block (Int.toBytes 8 7) 31) 24) = true
    ∧ cpGoValue (recvAt (WitCpMR.block (Int.toBytes 8 7) 33) 24) = true
    ∧ cpGoValue (recvAt (WitCpMR.block (Int.toBytes 8 7) 0) 24) = true := by decide

/-- Control: a header with `len > cap` is not a Go value. -/
theorem cpGoValue_rejects_bad : cpGoValue (List.replicate 24 0 ++ Int.toBytes 8 33 ++ Int.toBytes 8 32
    ++ List.replicate 32 0) = false := by decide

end E2e
