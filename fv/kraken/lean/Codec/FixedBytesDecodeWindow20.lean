import Codec.FixedBytesDecodeWindowOffsetZero
import Codec.Kind.FixedBytesDecodeWindow

/-!
# The fixed-bytes decode segment over windows for a 20-byte vector (new module)

`f = append(make([]byte, 0, 20), buf[src:src+20]...)` (Ethereum execution addresses: SourceAddress,
ToExecutionAddress, FeeRecipient, …). The code shape is that of the 32 / 48 / 96-byte fields with the size
immediate `0x14` (`mov $0x14,%ecx` before `callq runtime.makeslice` and `callq runtime.memmove`,
`movq $0x14,fC(%rdx)`, `movq $0x14,fL(%rdx)`). The statements `BytesDecWindow n rX rY` (`Codec/FixedBytesDecodeWindow.lean`) and
`BytesDecOffsetZeroWindow n rX rY` (`Codec/FixedBytesDecodeWindowOffsetZero.lean`) are already parametric in `n`; their collectors `bytesdec_seg_window` /
`bytesdec_seg_offset_zero_window` take `hn : n = 32 ∨ n = 48 ∨ n = 96` because each case runs the proof with a literal
immediate (a limit of the proof method, not of the statement). This module adds the case `n = 20`:

* `bytesdec_window_20_rX_rY` / `bytesdec_window_offset_zero_20_rX_rY`: one theorem per register pair (the same register sets),
  each proved by the proof text of `Codec/FixedBytesDecodeWindow.lean` / `Codec/FixedBytesDecodeWindowOffsetZero.lean` copied verbatim into a local macro (the
  model macros are `local`); only the literal size differs.
* `bytesdec_seg_window_size20`, `bytesdec_seg_offset_zero_window_size20`: the collectors at `n = 20`.
* `bytesDecSegKindWindow_of_size20`, `bytesDecSegOffsetZeroKindWindow_of_size20`: the kinds (`Codec/Kind/FixedBytesDecodeWindow.lean`, `Codec/FixedBytesDecodeWindowOffsetZero.lean`,
  unchanged, already parametric in `n`) proved from the collectors, as `bytesDecSegKindWindow_of`.

Contracts exactly as in the models: `MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 St` at count 20 (the count is a
bound variable of the contract) and `MemmoveContract St` (the byte count is `src.length`). No contract, statement or
existing module is changed. Heartbeat options = the model theorems' (16000000 add form, 4000000 offset-0 form).
-/

open Machine Runtime

namespace Codec

variable [Host]

set_option hygiene false in
/-- Proof text of one case (size, registers literal); the names are the binders of `BytesDecWindow`. -/
local macro "bytes_decode_window20_case " n:num rX:term:max rY:term:max : tactic => `(tactic| (
    replace heA : eraseNop qA = bytesDecHeadRegister $rX ($n : Int64) lff dR fL fC := heA
    replace heB : eraseNop qB = bytesDecMidRegisters $rX $rY ($n : Int64) lff lwb dR dB dS fP fL fC src := heB
    rw [show (OfNat.ofNat ($n : Nat) : Int) = ($n : Int) from rfl]
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo hjl hjm
    window_skip_leading_nops hqA
    window_step_directive hqA heA bytesDecHeadRegister 0
    window_skip_nops hqA heA 0
    window_step_directive hqA heA bytesDecHeadRegister 1
    intro _
    window_skip_nops hqA heA 1
    window_step_directive hqA heA bytesDecHeadRegister 2
    window_skip_nops hqA heA 2
    window_step_directive hqA heA bytesDecHeadRegister 3
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + nonNopIndex qA 3 + 1)) $n avail lo spl _
      rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
      (by dsimp only; rw [show sp - 8 + 8 = sp by bv_omega]; ecancel)) ?_
    rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
    dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
    subst hpc3
    obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
      zmms3, flags3, mem3⟩ := d3
    simp only at hrsp3 hr143 hrbp3 Hm3
    rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
    subst hrsp3 hr143 hrbp3
    rw [show sp - 8 + 8 = sp by bv_omega] at Hm3
    simp only [Nat.one_mul] at Hm3
    window_skip_nops hqA heA 3
    window_step_directive hqA heA bytesDecHeadRegister 4
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqA heA 4
    window_step_directive hqA heA bytesDecHeadRegister 5
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    unfold_step
    window_skip_nops hqA heA 5
    window_step_directive hqA heA bytesDecHeadRegister 6
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    unfold_step
    window_skip_nops hqA heA 6
    window_step_directive hqA heA bytesDecHeadRegister 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqA heA 7
    window_step_directive hqA heA bytesDecHeadRegister 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    window_step_directive hqB heB bytesDecMidRegisters 0
    window_skip_nops hqB heB 0
    window_step_directive hqB heB bytesDecMidRegisters 1
    apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    unfold_step
    window_skip_nops hqB heB 1
    window_step_directive hqB heB bytesDecMidRegisters 2
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m5' H5
    simp only [Width.bytes, Width.bits] at H5
    unfold_step
    window_skip_nops hqB heB 2
    window_step_directive hqB heB bytesDecMidRegisters 3
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 3
    window_step_directive hqB heB bytesDecMidRegisters 4
    window_skip_nops hqB heB 4
    window_step_directive hqB heB bytesDecMidRegisters 5
    window_skip_nops hqB heB 5
    window_step_directive hqB heB bytesDecMidRegisters 6
    apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + nonNopIndex qA 3 + 1)).toBitVec.toInt) _ _
      (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + nonNopIndex qB 6 + 1)) root (List.replicate $n 0) stk3 _
      (by rw [hroot]; rfl) (by simp [hroot]) hstk3
      (by dsimp only; rw [show src.toBitVec + bf = aSrc by rw [← hSrc]; exact BitVec.add_comm _ _]; ecancel)) ?_
    rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
    dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
    subst hpc4
    obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
      zmms4, flags4, mem4⟩ := d4
    simp only at hrsp4 hr144 hrbp4 Hm4
    rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp4
    subst hrsp4 hr144 hrbp4
    rw [show src.toBitVec + bf = aSrc by rw [← hSrc]; exact BitVec.add_comm _ _] at Hm4
    window_skip_nops hqB heB 6
    window_step_directive hqB heB bytesDecMidRegisters 7
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 7
    window_step_directive hqB heB bytesDecMidRegisters 8
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    unfold_step
    window_skip_nops hqB heB 8
    window_step_directive hqB heB bytesDecMidRegisters 9
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt ($n : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    unfold_step
    window_skip_nops hqB heB 9
    window_step_directive hqB heB bytesDecMidRegisters 10
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqB heB 10
    window_step_directive hqB heB bytesDecMidRegisters 11
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    window_skip_to_end hqB heB 11 hend
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt ($n : BitVec 64)) = Int.toBytes 8 $n by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩))


set_option hygiene false in
/-- Proof text of one case (size, registers literal); the names are the binders of `BytesDecOffsetZeroWindow`. -/
local macro "bytes_decode_window20_offset_zero_case " n:num rX:term:max rY:term:max : tactic => `(tactic| (
    replace heA : eraseNop qA = bytesDecHeadRegister $rX ($n : Int64) lff dR fL fC := heA
    replace heB : eraseNop qB = bytesDecMidOffsetZeroRegisters $rX $rY ($n : Int64) lff lwb dR dB dS fP fL fC := heB
    rw [show (OfNat.ofNat ($n : Nat) : Int) = ($n : Int) from rfl]
    obtain ⟨⟨rax, rbx, rcx, rdx, rsi, rdi, rsp, rbp, r8, r9, r10, r11, r12, r13, r14, r15⟩, zmms, flags, mem⟩ := s
    simp only at hrsp hrbp hr14 h_mem ⊢
    subst rsp rbp r14 hRet hLo hjl hjm
    window_skip_leading_nops hqA
    window_step_directive hqA heA bytesDecHeadRegister 0
    window_skip_nops hqA heA 0
    window_step_directive hqA heA bytesDecHeadRegister 1
    intro _
    window_skip_nops hqA heA 1
    window_step_directive hqA heA bytesDecHeadRegister 2
    window_skip_nops hqA heA 2
    window_step_directive hqA heA bytesDecHeadRegister 3
    apply store_step_at _ _ (sp - 8) _ _ _ rslot _ _ (by segment_addr) (by ecancel) (by exact hrs)
    intro m1' H1
    simp only [Width.bytes, Width.bits] at H1
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hms _ (Host.addrOf (j1 + nonNopIndex qA 3 + 1)) $n avail lo spl _
      rfl (by simp) (by rfl) (by omega) (by unfold maxAlloc; omega) (by omega) hlo hspl
      (by dsimp only; rw [show sp - 8 + 8 = sp by bv_omega]; ecancel)) ?_
    rintro ⟨d3, pc3⟩ ⟨hpc3, hrsp3, hr143, hrbp3, stk3, spm3, hstk3, hspm3, Hm3⟩
    dsimp only at hpc3 hrsp3 hr143 hrbp3 Hm3
    subst hpc3
    obtain ⟨⟨rax3, rbx3, rcx3, rdx3, rsi3, rdi3, rsp3, rbp3, r83, r93, r103, r113, r123, r133, r143, r153⟩,
      zmms3, flags3, mem3⟩ := d3
    simp only at hrsp3 hr143 hrbp3 Hm3
    rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp3
    subst hrsp3 hr143 hrbp3
    rw [show sp - 8 + 8 = sp by bv_omega] at Hm3
    simp only [Nat.one_mul] at Hm3
    window_skip_nops hqA heA 3
    window_step_directive hqA heA bytesDecHeadRegister 4
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqA heA 4
    window_step_directive hqA heA bytesDecHeadRegister 5
    apply store_step_at _ _ aL _ _ _ vL _ _ (by rw [← hL]) (by ecancel) (by exact hvL)
    intro m2' H2
    simp only [Width.bytes, Width.bits] at H2
    unfold_step
    window_skip_nops hqA heA 5
    window_step_directive hqA heA bytesDecHeadRegister 6
    apply store_step_at _ _ aC _ _ _ vC _ _ (by rw [← hC]) (by ecancel) (by exact hvC)
    intro m3' H3
    simp only [Width.bytes, Width.bits] at H3
    unfold_step
    window_skip_nops hqA heA 6
    window_step_directive hqA heA bytesDecHeadRegister 7
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqA heA 7
    window_step_directive hqA heA bytesDecHeadRegister 8
    split
    case isFalse h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    rw [hl]
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 0
    window_skip_nops hqB heB 0
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 1
    apply store_step_at _ _ aS _ _ _ lS _ _ (by rw [← hS]) (by ecancel) (by exact hlS)
    intro m4' H4
    simp only [Width.bytes, Width.bits] at H4
    unfold_step
    window_skip_nops hqB heB 1
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 2
    apply store_step_at _ _ aP _ _ _ vP _ _ (by rw [← hP]) (by ecancel) (by exact hvP)
    intro m5' H5
    simp only [Width.bytes, Width.bits] at H5
    unfold_step
    window_skip_nops hqB heB 2
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 3
    apply load_step_at _ _ aB _ _ (Int.toBytes 8 bf.toInt) _ _ (by rw [← hB']) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 3
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 4
    window_skip_nops hqB heB 4
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 5
    apply store_step_at _ _ (sp - 8) _ _ _ (Int.toBytes 8 (Host.addrOf (j1 + nonNopIndex qA 3 + 1)).toBitVec.toInt) _ _
      (by segment_addr) (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m6' H6
    simp only [Width.bytes, Width.bits] at H6
    unfold_step
    try rw [show sp - 8#64 = sp - 8 from rfl] at *
    refine eventually_trans _ _ _ _ (hmm _ (Host.addrOf (j2 + nonNopIndex qB 5 + 1)) root (List.replicate $n 0) stk3 _
      (by rw [hroot]; rfl) (by simp [hroot]) hstk3
      (by dsimp only; ecancel)) ?_
    rintro ⟨d4, pc4⟩ ⟨hpc4, hrsp4, hr144, hrbp4, stk4, hstk4, Hm4⟩
    dsimp only at hpc4 hrsp4 hr144 hrbp4 Hm4
    subst hpc4
    obtain ⟨⟨rax4, rbx4, rcx4, rdx4, rsi4, rdi4, rsp4, rbp4, r84, r94, r104, r114, r124, r134, r144, r154⟩,
      zmms4, flags4, mem4⟩ := d4
    simp only at hrsp4 hr144 hrbp4 Hm4
    rw [show ({ toBitVec := sp - 8 } + 8 : UInt64) = { toBitVec := sp } by
      apply UInt64.toBitVec_inj.mp; simp only [UInt64.toBitVec_add, UInt64.toBitVec_ofNat]; bv_omega] at hrsp4
    subst hrsp4 hr144 hrbp4
    window_skip_nops hqB heB 5
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 6
    apply load_step_at _ _ aR _ _ (Int.toBytes 8 rcv.toInt) _ _ (by rw [← hR]) (by ecancel)
      (by exact Int.toBytes_length 8 _)
    unfold_step
    window_skip_nops hqB heB 6
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 7
    apply store_step_at _ _ aL _ _ _ (Int.toBytes 8 (BitVec.toInt (0 : BitVec 64))) _ _ (by rw [← hL])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m7' H7
    simp only [Width.bytes, Width.bits] at H7
    unfold_step
    window_skip_nops hqB heB 7
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 8
    apply store_step_at _ _ aC _ _ _ (Int.toBytes 8 (BitVec.toInt ($n : BitVec 64))) _ _ (by rw [← hC])
      (by ecancel) (by exact Int.toBytes_length 8 _)
    intro m8' H8
    simp only [Width.bytes, Width.bits] at H8
    unfold_step
    window_skip_nops hqB heB 8
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 9
    apply load_step _ _ _ _ [0, 0, 0, 0] _ _ (by ecancel) (by simp)
    simp only [show Int.ofBytes [0, 0, 0, 0] = 0 by simp [Int.ofBytes]]
    unfold_step
    window_skip_nops hqB heB 9
    window_step_directive hqB heB bytesDecMidOffsetZeroRegisters 10
    split
    case isTrue h => exfalso; simp [CondCode.interp, StatusFlags.from_result] at h
    simp only [Effects.All]
    window_skip_to_end hqB heB 10 hend
    apply Eventually.done
    simp only [show Int.toBytes 8 (BitVec.toInt ($n : BitVec 64)) = Int.toBytes 8 $n by decide] at H8
    exact ⟨rfl, rfl, rfl, rfl, rax3.toBitVec, spm3, stk4, hspm3, hstk4, rfl, by ecancel⟩))


set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rdx_rax : BytesDecWindow 20 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rdx Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rdx_rcx : BytesDecWindow 20 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rdx_rdx : BytesDecWindow 20 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rdx_rsi : BytesDecWindow 20 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rdx_rdi : BytesDecWindow 20 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rsi_rax : BytesDecWindow 20 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rsi Reg64.rax

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rsi_rcx : BytesDecWindow 20 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rsi_rdx : BytesDecWindow 20 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rsi_rsi : BytesDecWindow 20 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_20_rsi_rdi : BytesDecWindow 20 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC src qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC aSrc St hR hB' hS hRet hLo hP hL hC hSrc rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_case 20 Reg64.rsi Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rdx_rax : BytesDecOffsetZeroWindow 20 Reg64.rdx Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rdx Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rdx_rcx : BytesDecOffsetZeroWindow 20 Reg64.rdx Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rdx Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rdx_rdx : BytesDecOffsetZeroWindow 20 Reg64.rdx Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rdx Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rdx_rsi : BytesDecOffsetZeroWindow 20 Reg64.rdx Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rdx Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rdx_rdi : BytesDecOffsetZeroWindow 20 Reg64.rdx Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rdx Reg64.rdi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rsi_rax : BytesDecOffsetZeroWindow 20 Reg64.rsi Reg64.rax := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rsi Reg64.rax

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rsi_rcx : BytesDecOffsetZeroWindow 20 Reg64.rsi Reg64.rcx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rsi Reg64.rcx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rsi_rdx : BytesDecOffsetZeroWindow 20 Reg64.rsi Reg64.rdx := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rsi Reg64.rdx

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rsi_rsi : BytesDecOffsetZeroWindow 20 Reg64.rsi Reg64.rsi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rsi Reg64.rsi

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem bytesdec_window_offset_zero_20_rsi_rdi : BytesDecOffsetZeroWindow 20 Reg64.rsi Reg64.rdi := by
  intro lff lwb dR dB dS fP fL fC qA qB j1 j2 jl jm e hqA heA hqB heB hjl hl hjm hend sp rcv bf aR aB aS aRet aLo aP aL aC St hR hB' hS hRet hLo hP hL hC rbp0 r140 root hroot spl rslot lo lS vP vL vC hspl hrs hlo hlS hvP hvL hvC R Heap avail hav s hrsp hrbp hr14 h_mem hms hmm
  bytes_decode_window20_offset_zero_case 20 Reg64.rsi Reg64.rdi

/-- **20-byte decode segment over windows, receiver registers as parameters** (add form). -/
theorem bytesdec_seg_window_size20 (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi) :
    BytesDecWindow 20 rX rY := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytesdec_window_20_rdx_rax
    | exact bytesdec_window_20_rdx_rcx
    | exact bytesdec_window_20_rdx_rdx
    | exact bytesdec_window_20_rdx_rsi
    | exact bytesdec_window_20_rdx_rdi
    | exact bytesdec_window_20_rsi_rax
    | exact bytesdec_window_20_rsi_rcx
    | exact bytesdec_window_20_rsi_rdx
    | exact bytesdec_window_20_rsi_rsi
    | exact bytesdec_window_20_rsi_rdi

/-- **20-byte decode segment over windows, receiver registers as parameters** (offset-0 form). -/
theorem bytesdec_seg_offset_zero_window_size20 (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi) :
    BytesDecOffsetZeroWindow 20 rX rY := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact bytesdec_window_offset_zero_20_rdx_rax
    | exact bytesdec_window_offset_zero_20_rdx_rcx
    | exact bytesdec_window_offset_zero_20_rdx_rdx
    | exact bytesdec_window_offset_zero_20_rdx_rsi
    | exact bytesdec_window_offset_zero_20_rdx_rdi
    | exact bytesdec_window_offset_zero_20_rsi_rax
    | exact bytesdec_window_offset_zero_20_rsi_rcx
    | exact bytesdec_window_offset_zero_20_rsi_rdx
    | exact bytesdec_window_offset_zero_20_rsi_rsi
    | exact bytesdec_window_offset_zero_20_rsi_rdi

/-- `bytesDecSegKindWindow` at `n = 20` follows from `bytesdec_seg_window_size20` and the window facts of an instance. -/
theorem bytesDecSegKindWindow_of_size20 (C : Program) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi)
    (j1 j2 jl jm e : Nat) (lff lwb : String) (dR dB dS fP fL fC src : Int64) (qA qB : Program)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = bytesDecHeadRegister rX (OfNat.ofNat 20) lff dR fL fC)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = bytesDecMidRegisters rX rY (OfNat.ofNat 20) lff lwb dR dB dS fP fL fC src)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + jl))
    (hjm : j2 + nonNopIndex qB 6 = jm) (hend : j2 + qB.length = e) :
    bytesDecSegKindWindow 20 C rY j1 jm e dR dB dS fP fL fC src :=
  fun k hk hf => bytesdec_seg_window_size20 rX rY hX hY lff lwb dR dB dS fP fL fC src qA qB (k + j1) (k + j2) (k + jl)
    (k + jm) (k + e) (hqA k hk) heA (hqB k hk) heB (by omega) (hl k hk hf) (by omega) (by omega)

/-- `bytesDecSegOffsetZeroKindWindow` at `n = 20` follows from `bytesdec_seg_offset_zero_window_size20` and the window facts of an instance. -/
theorem bytesDecSegOffsetZeroKindWindow_of_size20 (C : Program) (rX rY : Reg64)
    (hX : rX = Reg64.rdx ∨ rX = Reg64.rsi)
    (hY : rY = Reg64.rax ∨ rY = Reg64.rcx ∨ rY = Reg64.rdx ∨ rY = Reg64.rsi ∨ rY = Reg64.rdi)
    (j1 j2 jl jm e : Nat) (lff lwb : String) (dR dB dS fP fL fC : Int64) (qA qB : Program)
    (hqA : ∀ k, C.IsInfixAt Host.prog k → qA.IsInfixAt Host.prog (k + j1))
    (heA : eraseNop qA = bytesDecHeadRegister rX (OfNat.ofNat 20) lff dR fL fC)
    (hqB : ∀ k, C.IsInfixAt Host.prog k → qB.IsInfixAt Host.prog (k + j2))
    (heB : eraseNop qB = bytesDecMidOffsetZeroRegisters rX rY (OfNat.ofNat 20) lff lwb dR dB dS fP fL fC)
    (hjl : j2 + nonNopIndex qB 0 = jl)
    (hl : ∀ k, C.IsInfixAt Host.prog k → LabelsFresh C k → label lff = Host.addrOf (k + jl))
    (hjm : j2 + nonNopIndex qB 5 = jm) (hend : j2 + qB.length = e) :
    bytesDecSegOffsetZeroKindWindow 20 C rY j1 jm e dR dB dS fP fL fC :=
  fun k hk hf => bytesdec_seg_offset_zero_window_size20 rX rY hX hY lff lwb dR dB dS fP fL fC qA qB (k + j1) (k + j2) (k + jl)
    (k + jm) (k + e) (hqA k hk) heA (hqB k hk) heB (by omega) (hl k hk hf) (by omega) (by omega)

end Codec
