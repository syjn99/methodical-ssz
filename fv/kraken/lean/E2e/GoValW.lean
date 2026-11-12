import E2e.GoVal
import E2e.WitCpW
import E2e.WitCpWR

/-!
# Go-value element for the encoder cover witnesses

`WitCpW` (cover witness): the receiver is at offset 9016 of the block (rax = 0x12338),
`Root` = (0x12380, 32, 32). `WitCpWR` (reject cover witness): the receiver is at offset 9032
(rax = 0x12348), `Root` = (0x5000, rl, 48).

`WitCpWR.rej_runs` is stated for every `rl ≠ 32`. Only `rl ≤ 48` (= cap of the Root header) gives a Go
value: `witCpWR_recv` checks rl 0, 31, 33 (the instances used) and 48 (the maximum); the control
`witCpWR_recv_bad` shows rl 49 is not a Go value. The machine theorem itself does not need `rl ≤ cap`
(the code compares `len(Root)` with 32 only); a Go caller can only reach it with `rl ≤ 48`.

The receiver bytes do not depend on `dst` (it is after the receiver in the block); the checks use
`dst = []` and the epoch bytes `Int.toBytes 8 7`, as `witCpMR_recv` does.
-/

namespace E2e

set_option maxRecDepth 1000000

/-- Cover witness receiver: a Go value, and its exact bytes. -/
theorem witCpW_recv : cpGoValue (recvAt (WitCpW.block (Int.toBytes 8 7) (List.replicate 32 0xff) []) 9016) = true
    ∧ recvAt (WitCpW.block (Int.toBytes 8 7) (List.replicate 32 0xff) []) 9016
      = List.replicate 8 0 ++ Int.toBytes 8 7 ++ Int.toBytes 8 0x12380 ++ Int.toBytes 8 32 ++ Int.toBytes 8 32
        ++ List.replicate 32 0 := by decide

/-- Reject cover witness receivers: `len(Root)` 0, 31, 33, 48 with cap 48 are Go values. -/
theorem witCpWR_recv : cpGoValue (recvAt (WitCpWR.block (Int.toBytes 8 7) 0 []) 9032) = true
    ∧ cpGoValue (recvAt (WitCpWR.block (Int.toBytes 8 7) 31 []) 9032) = true
    ∧ cpGoValue (recvAt (WitCpWR.block (Int.toBytes 8 7) 33 []) 9032) = true
    ∧ cpGoValue (recvAt (WitCpWR.block (Int.toBytes 8 7) 48 []) 9032) = true := by decide

/-- Control: `len(Root)` 49 > cap 48 (allowed by `rej_runs`) is not a Go value. -/
theorem witCpWR_recv_bad : cpGoValue (recvAt (WitCpWR.block (Int.toBytes 8 7) 49 []) 9032) = false := by decide

end E2e
