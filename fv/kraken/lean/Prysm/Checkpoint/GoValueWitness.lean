import Prysm.Checkpoint.GoValue
import Prysm.Checkpoint.WitnessEncodeCover
import Prysm.Checkpoint.WitnessEncodeRejectLengthCover

/-!
# Go-value element for the encoder cover witnesses

`Prysm/Checkpoint/WitnessEncodeCover.lean` (cover witness): the receiver is at offset 9016 of the block (rax = 0x12338),
`Root` = (0x12380, 32, 32). `Prysm/Checkpoint/WitnessEncodeRejectLengthCover.lean` (reject cover witness): the receiver is at offset 9032
(rax = 0x12348), `Root` = (0x5000, rl, 48).

`Witness.EncodeRejectLengthCover.runs` is stated for every `rl ≠ 32`. Only `rl ≤ 48` (= cap of the Root header) gives a Go
value: `witness_encode_reject_length_cover_recv` checks rl 0, 31, 33 (the instances used) and 48 (the maximum); the control
`witness_encode_reject_length_cover_recv_bad` shows rl 49 is not a Go value. The machine theorem itself does not need `rl ≤ cap`
(the code compares `len(Root)` with 32 only); a Go caller can only reach it with `rl ≤ 48`.

The receiver bytes do not depend on `dst` (it is after the receiver in the block); the checks use
`dst = []` and the epoch bytes `Int.toBytes 8 7`, as `witness_encode_reject_length_recv` does.
-/

namespace Prysm.Checkpoint

set_option maxRecDepth 1000000

/-- Cover witness receiver: a Go value, and its exact bytes. -/
theorem witness_encode_cover_recv : goValue (recvAt (Witness.EncodeCover.block (Int.toBytes 8 7) (List.replicate 32 0xff) []) 9016) = true
    ∧ recvAt (Witness.EncodeCover.block (Int.toBytes 8 7) (List.replicate 32 0xff) []) 9016
      = List.replicate 8 0 ++ Int.toBytes 8 7 ++ Int.toBytes 8 0x12380 ++ Int.toBytes 8 32 ++ Int.toBytes 8 32
        ++ List.replicate 32 0 := by decide

/-- Reject cover witness receivers: `len(Root)` 0, 31, 33, 48 with cap 48 are Go values. -/
theorem witness_encode_reject_length_cover_recv : goValue (recvAt (Witness.EncodeRejectLengthCover.block (Int.toBytes 8 7) 0 []) 9032) = true
    ∧ goValue (recvAt (Witness.EncodeRejectLengthCover.block (Int.toBytes 8 7) 31 []) 9032) = true
    ∧ goValue (recvAt (Witness.EncodeRejectLengthCover.block (Int.toBytes 8 7) 33 []) 9032) = true
    ∧ goValue (recvAt (Witness.EncodeRejectLengthCover.block (Int.toBytes 8 7) 48 []) 9032) = true := by decide

/-- Control: `len(Root)` 49 > cap 48 (allowed by `Witness.EncodeRejectLengthCover.runs`) is not a Go value. -/
theorem witness_encode_reject_length_cover_recv_bad : goValue (recvAt (Witness.EncodeRejectLengthCover.block (Int.toBytes 8 7) 49 []) 9032) = false := by decide

end Prysm.Checkpoint
