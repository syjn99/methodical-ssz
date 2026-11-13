import Prysm.Checkpoint.DecodeAccept
import Prysm.Checkpoint.EncodeFastPath
import Prysm.Checkpoint.DecodeThenEncodeReceiver

/-!
# Machine-level composition decoder → encoder (real Go 1.26.10 code)

`DecodeThenEncode.round_trip` (it runs the decoder; the older theorem now in `Prysm/Checkpoint/DecodeThenEncodeReceiver.lean` did not): start at the
**entry of `(*Checkpoint).UnmarshalSSZ`** with the premises of
`Decode.accept` (40 input bytes `e8 ++ root`, any receiver contents). The
decoder runs (with the real `(*primitives.Epoch).UnmarshalSSZ` through
`Prysm.Epoch.Decode.accept_function_spec_holds`, no Epoch hypothesis) and returns nil to `ra`. The caller then
calls `(*Checkpoint).MarshalSSZTo` on the same receiver (`hupd`: the call
writes a new return address `ra2` into the same return slot, the rest of the
memory is unchanged) with `dst = (dptr, dlen, cap)`; the encoder returns at
`ra2` with `(dptr, dlen + 40, nil)`, the prefix unchanged, and
`dst[dlen..dlen+40]` = the 40 input bytes. The input bytes are unchanged.

Frame mapping (x = rsp at the decoder entry = rsp at the encoder entry):
the decoder leaves the saved rbp at x − 8, the rbx spill at x + 16, `p` at
x − 32 and two zero words at x − 48, x − 40; these are the encoder's `fp`, `s2`,
`l32` and `t30`. The encoder slots x − 16, x − 24 and x − 64 … x − 49 are not in
the decoder's footprint: the caller passes them (`g16`, `g24`, `g64`) with dst.
The encoder's return slot x − 120 and its scratch below are the low part of the
decoder's scratch (`S ≥ 24`, encoder scratch `S − 24`); the decoder's 24-byte
spill block at x − 88, its return slot x − 96 and 16 scratch bytes at x − 112
are frame of the encoder call.
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

theorem DecodeThenEncode.scr (x : BitVec 64) (S : Nat) (h : 24 ≤ S) (hS : S < 2 ^ 60) (L : List UInt8) (hL : L.length = S) :
    Eq (L.At (x - 96 - BitVec.ofNat 64 S)) =
      Eq ((L.take (S - 24)).At (x - 120 - BitVec.ofNat 64 (S - 24)))
        ⋆ Eq (((L.drop (S - 24)).take 8).At (x - 120)) ⋆ Eq (((L.drop (S - 24)).drop 8).At (x - 112)) := by
  have e1 : Eq (L.At (x - 96 - BitVec.ofNat 64 S)) =
      Eq ((L.take (S - 24)).At (x - 96 - BitVec.ofNat 64 S)) ⋆ Eq ((L.drop (S - 24)).At (x - 120)) := by
    conv => lhs; rw [← List.take_append_drop (S - 24) L]
    refine at_app _ _ ?_ (by simp [hL]; omega)
    rw [List.length_take, hL, Nat.min_eq_left (by omega)]
    checkpoint_addr
  have e2 : Eq ((L.drop (S - 24)).At (x - 120)) =
      Eq (((L.drop (S - 24)).take 8).At (x - 120)) ⋆ Eq (((L.drop (S - 24)).drop 8).At (x - 112)) := by
    conv => lhs; rw [← List.take_append_drop 8 (L.drop (S - 24))]
    refine at_app _ _ ?_ (by simp [hL]; omega)
    rw [List.length_take, List.length_drop, hL, show min 8 (S - (S - 24)) = 8 by omega]
    bv_omega
  have e3 : x - 96 - BitVec.ofNat 64 S = x - 120 - BitVec.ofNat 64 (S - 24) := by checkpoint_addr
  rw [e1, e2, e3, Std.ExtHashMap.sep_assoc]

theorem DecodeThenEncode.t30 (x : BitVec 64) :
    Eq ((Int.toBytes 8 0 ++ Int.toBytes 8 0).At (x - 48)) =
      Eq ((Int.toBytes 8 0).At (x - 48)) ⋆ Eq ((Int.toBytes 8 0).At (x - 40)) :=
  at_app _ _ (by rw [Int.toBytes_length]; bv_omega) (by simp [Int.toBytes_length])

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Machine-level composition.** Decoder entry → `Decode.accept` → (caller: `hupd`) →
`Encode.fast_path` → encoder return; output = `dst ++ (e8 ++ root)`, the 40
input bytes. -/
theorem DecodeThenEncode.round_trip (kd : Nat) (hkd : unmarshalSSZ.IsInfixAt Host.prog kd)
    (hfd : LabelsFresh unmarshalSSZ kd)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (km : Nat) (hkm : marshalSSZTo.IsInfixAt Host.prog km) (hfm : LabelsFresh marshalSSZTo km)
    (e8 root : List UInt8) (he8 : e8.length = 8) (hroot : root.length = 32)
    (s : MachineData) (ra ra2 guard : UInt64)
    (fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl g16 g24 g64 pre d0 d1 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (hl20 : l20.length = 8)
    (hl28 : l28.length = 8) (hl30 : l30.length = 8) (hm0 : m0.length = 8) (hm1 : m1.length = 8)
    (hm2 : m2.length = 8) (hrs : rslot.length = 8) (hcst : cst.length = 8) (hc0 : c0.length = 8)
    (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8) (hctl : ctl.length = 32)
    (hg16 : g16.length = 8) (hg24 : g24.length = 8) (hg64 : g64.length = 16)
    (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat)
    (hcap2 : dlen.toNat + 40 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63)
    (R0 : DataMem → Prop) (S : Nat) (hS24 : 24 ≤ S) (hS : S < 2 ^ 60) (scratch : List UInt8)
    (hsc : scratch.length = S)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (s.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (m2.At (s.regs.rsp.toBitVec - 72)) ⋆ Eq (m1.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq (m0.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At s.regs.rbx.toBitVec) ⋆ Eq (root.At (s.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (c0.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (s.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (s.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ (Eq (g16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (g24.At (s.regs.rsp.toBitVec - 24))
        ⋆ Eq (g64.At (s.regs.rsp.toBitVec - 64))
        ⋆ Eq (pre.At dptr.toBitVec) ⋆ Eq (d0.At (dptr.toBitVec + dlen.toBitVec))
        ⋆ Eq (d1.At (dptr.toBitVec + dlen.toBitVec + 8)) ⋆ R0))
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 40) (hav : 32 ≤ avail)
    (hms : MakesliceC Heap ElfData.PrysmTarget.e2eU8Type_addr 1 S) (hmm : MemmoveC S) (hmm2 : MemmoveC (S - 24)) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧ st.data.regs.rbx = 0 ∧
        ∀ (mem2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) mem2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx.toNat = dlen.toNat + 40 ∧ st'.data.regs.rcx = cap
              ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0 ∧
              (Eq (pre.At dptr.toBitVec) ⋆ Eq ((e8 ++ root).At (dptr.toBitVec + dlen.toBitVec))
                ⋆ Eq ((e8 ++ root).At s.regs.rbx.toBitVec) ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp },
              zm, fl, mem2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf kd⟩ := by
  refine eventually_trans _ _ _ _ (Decode.accept kd hkd hfd kE hkE hfE e8 root he8 hroot s ra guard
    fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0
    hcP hcL hcC hctl _ S (by omega) hS scratch hsc Heap avail h_mem hguard hlen hav hms hmm) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, hrbx, -, -, hr14, p, scr, mm, hscr, -, hm⟩
  refine Eventually.done _ ⟨hpc, hrax, hrbx, fun mem2 zm fl hupd => ?_⟩
  rw [DecodeThenEncode.scr _ S hS24 hS scr hscr] at hm
  simp only [Std.ExtHashMap.sep_assoc] at hm
  have hmem2 := hupd _ (by ecancel)
  refine eventually_trans _ _ _ _ (Encode.fast_path km hkm hfm cst e8 (Int.toBytes 8 32) ctl root pre d0 d1
    hcst he8 (Int.toBytes_length 8 _) hctl hroot hd0 hd1 p _ ra2 guard (by dsimp only; exact hpre)
    (Int.toBytes 8 s.regs.rbp.toBitVec.toInt) (Int.toBytes 8 s.regs.rbx.toBitVec.toInt) g16 g24
    (Int.toBytes 8 p.toInt) g64 (Int.toBytes 8 0 ++ Int.toBytes 8 0) ((scr.drop (S - 24)).take 8)
    (Int.toBytes_length 8 _) (Int.toBytes_length 8 _) hg16 hg24 (Int.toBytes_length 8 _) hg64
    (by simp [Int.toBytes_length]) (by simp [hscr]; try omega) _ (S - 24) (scr.take (S - 24)) (by simp [hscr]; try omega)
    (by
      dsimp only
      rw [hr14, DecodeThenEncode.t30]
      ecancel)
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; exact hcap63) hmm2) ?_
  intro st' hh
  obtain ⟨e1, e2, e3, e4, e5, e6, -, -, -, t, u, scr', -, -, -, hm'⟩ := hh
  dsimp only at e2 e3 e4 hm'
  refine Eventually.done _ ⟨e1, e2, e3, e4, e5, e6, ?_⟩
  rw [at_app e8 root (b := dptr.toBitVec + dlen.toBitVec + 8) (by rw [he8]; rfl) (by simp [he8, hroot]),
    at_app e8 root (b := s.regs.rbx.toBitVec + 8) (by rw [he8]; rfl) (by simp [he8, hroot])]
  exact sep_true (by ecancel)

end Prysm.Checkpoint
