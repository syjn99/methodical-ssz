import Fk.BvSpec

/-!
# Composition check: decode, then marshal the same receiver (re-proof R7)

`bv_unmarshal_then_marshal`: BitVec.UnmarshalSSZ on a canonical byte `b`
returns to the caller; the caller then calls BitVec.MarshalSSZTo on the same
receiver (`call` writes a new return address `ra2` into the same return slot,
`hupd`), and the encoder appends `b` to dst.

No premise of the second call is assumed: the receiver graph J = (p, 1, 1),
`[b]` at p, the saved-rbp slot, the spill slots, the return slot, the scratch
and the stack guard all come from the conclusion of `bv_accept_main`. The
decoder's scratch (`S ≥ 16` bytes) is reused: its top 8 bytes become the
encoder's call slot, the rest the encoder's scratch. Only the caller's own
slots (rsp + 24, rsp + 32) and the destination are in the frame `R0`.
-/

open Fk Fk.Code
variable [Host]

theorem cmp_scr (x : BitVec 64) (S : Nat) (h : 16 ≤ S) (h2 : S < 2 ^ 64) :
    x - 88 - BitVec.ofNat 64 S + BitVec.ofNat 64 (S - 8) = x - 96 := by
  have : BitVec.ofNat 64 (S - 8) = BitVec.ofNat 64 S - 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [this]; bv_omega
theorem cmp_scr' (x : BitVec 64) (S : Nat) (h : 16 ≤ S) :
    x - 88 - BitVec.ofNat 64 S = x - 96 - BitVec.ofNat 64 (S - 8) := by
  have : BitVec.ofNat 64 (S - 8) = BitVec.ofNat 64 S - 8 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  rw [this]; bv_omega
theorem cmp_back (x : BitVec 64) (c : Nat) : x - 96 - BitVec.ofNat 64 c + BitVec.ofNat 64 c = x - 96 := by bv_omega
theorem cmp_one : Int.toBytes 8 (1 : BitVec 64).toInt = Int.toBytes 8 1 := by decide
theorem cmp_one' : Int.toBytes 8 (1 : UInt64).toBitVec.toInt = Int.toBytes 8 1 := by decide

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem bv_unmarshal_then_marshal (kd : Nat) (hkd : BitVecUnmarshalSSZ.IsInfixAt Host.prog kd)
    (hfd : LabelsFresh BitVecUnmarshalSSZ kd)
    (km : Nat) (hkm : BitVecMarshalSSZTo.IsInfixAt Host.prog km) (hfm : LabelsFresh BitVecMarshalSSZTo km)
    (b : UInt8) (hb : b.toNat < 16) (s : MachineData) (ra ra2 guard : UInt64)
    (fp s1 s2 f40 f32 rslot cP cL cC sl3 sl4 pre d0 : List UInt8)
    (hfp : fp.length = 8) (h1 : s1.length = 8) (h2 : s2.length = 8) (h40 : f40.length = 8) (h32 : f32.length = 8)
    (hrs : rslot.length = 8) (hcP : cP.length = 8) (hcL : cL.length = 8) (hcC : cC.length = 8)
    (hl3 : sl3.length = 8) (hl4 : sl4.length = 8) (hd0 : d0.length = 1)
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat)
    (hcap : dlen.toNat + 1 ≤ cap.toNat) (hcap63 : cap.toNat < 2 ^ 63)
    (R0 : DataMem → Prop) (S : Nat) (scratch spm : List UInt8) (hsc : scratch.length = S) (h16S : 16 ≤ S)
    (hspm : spm.length = 24)
    (Heap : Nat → DataMem → Prop) (avail : Nat)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (s.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (f40.At (s.regs.rsp.toBitVec - 40)) ⋆ Eq (f32.At (s.regs.rsp.toBitVec - 32))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 88)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 88 - BitVec.ofNat 64 S))
      ⋆ Eq (spm.At (s.regs.rsp.toBitVec - 80))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq ([b].At s.regs.rbx.toBitVec)
      ⋆ Eq (cP.At s.regs.rax.toBitVec) ⋆ Eq (cL.At (s.regs.rax.toBitVec + 8)) ⋆ Eq (cC.At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec)
      ⋆ (Eq (sl3.At (s.regs.rsp.toBitVec + 24)) ⋆ Eq (sl4.At (s.regs.rsp.toBitVec + 32))
        ⋆ Eq (pre.At dptr.toBitVec) ⋆ Eq (d0.At (dptr.toBitVec + dlen.toBitVec)) ⋆ R0))
    (hguard : guard.toNat + 96 < s.regs.rsp.toNat) (hsp : 104 + S ≤ s.regs.rsp.toNat)
    (hlen : s.regs.rcx = 1) (hav : 1 * 1 ≤ avail)
    (hvbv : VbvAccC) (hms : MakesliceC Heap (label "type__" + 48736).toBitVec 1 S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧
        ∀ (m2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) m2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx.toNat = dlen.toNat + 1 ∧ st'.data.regs.rdi = 0 ∧
              (Eq (pre.At dptr.toBitVec) ⋆ Eq ([b].At (dptr.toBitVec + dlen.toBitVec)) ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp },
              zm, fl, m2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf kd⟩ := by
  refine eventually_trans _ _ _ _ (bv_accept_main kd hkd hfd b hb s ra guard fp s1 s2 f40 f32 rslot cP cL cC
    hfp h1 h2 h40 h32 hrs hcP hcL hcC _ S scratch spm hsc (by omega) hspm Heap avail h_mem (by omega) (by omega)
    hlen hav hvbv hms) ?_
  rintro ⟨d, pc⟩ ⟨hpc, hrax, -, -, -, hr14, p, fp', s1', s2', f40', f32', rs', sc', spm', hfp', hs1', hs2', -, -, hrs',
    hsc', hspm', hm⟩
  refine Eventually.done _ ⟨hpc, hrax, fun m2 zm fl hupd => ?_⟩
  -- the call slot of the encoder is the top of the decoder's scratch
  have hS64 : S < 2 ^ 64 := by have := s.regs.rsp.toNat_lt_size; simp only [UInt64.size] at this; omega
  rw [← List.take_append_drop (S - 8) sc', Mem.At_append_sep _ _ _ (by simp [hsc']; omega)] at hm
  simp only [List.length_take, hsc', show min (S - 8) S = S - 8 by omega, cmp_scr _ S h16S hS64,
    cmp_scr' _ S h16S, cmp_back] at hm
  have hm2 := hupd _ (by ecancel)
  have hr : (s.regs.rsp.toBitVec : BitVec 64) = s.regs.rsp.toBitVec := rfl
  refine eventually_trans _ _ _ _ (bv_marshal_main km hkm hfm b hb p 1 _ ra2 guard pre d0 fp' s1' s2' sl3 sl4
    (sc'.drop (S - 8)) rs' (sc'.take (S - 8)) hd0 hfp' hs1' hs2' hl3 hl4 (by simp [hsc']; omega) hrs' (S - 8)
    (by simp [hsc']) (by omega) _
    (by
      dsimp only
      rw [hr14, cmp_one, cmp_one']
      ecancel)
    (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; omega) (by dsimp only; exact hcap63) hvbv) ?_
  intro st' hh
  obtain ⟨e1, e2, e3, -, e5, -, -, -, -, f1, f2, f3, f4, f5, f6, f7, f8, -, -, -, -, -, -, -, -, hm'⟩ := hh
  dsimp only at e2 e3 hm'
  exact Eventually.done _ ⟨e1, e2, e3, e5, sep_true (by ecancel)⟩
