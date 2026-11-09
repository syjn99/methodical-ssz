import Fk.ScAccept
import Fk.ScMarshal

/-!
# Scalars: decode, then marshal the same receiver

`sc_unmarshal_then_marshal`: Scalars.UnmarshalSSZ on 16 bytes `b0..b4`
(bool byte 0 or 1) returns nil; the caller then calls Scalars.MarshalSSZTo on
the same receiver (`hupd`: the call writes `ra2` into the same return slot) and
-/

open Fk Fk.Code
variable [Host]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem sc_unmarshal_then_marshal (kd : Nat) (hkd : ScalarsUnmarshalSSZ.IsInfixAt Host.prog kd)
    (km : Nat) (hkm : ScalarsMarshalSSZTo.IsInfixAt Host.prog km) (hfm : LabelsFresh ScalarsMarshalSSZTo km)
    (s : MachineData) (ra ra2 guard : UInt64) (slot b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 fp sp1 d0 d1 d2 d3 d4 pre : List UInt8)
    (hsl : slot.length = 8) (h0l : b0.length = 1) (h1l : b1.length = 2) (h2l : b2.length = 4)
    (h3l : b3.length = 8) (h4l : b4.length = 1)
    (g0 : c0.length = 1) (g1 : c1.length = 2) (g2 : c2.length = 4) (g3 : c3.length = 8) (g4 : c4.length = 1)
    (hfp : fp.length = 8) (hs1 : sp1.length = 8)
    (hd0 : d0.length = 1) (hd1 : d1.length = 2) (hd2 : d2.length = 4) (hd3 : d3.length = 8) (hd4 : d4.length = 1)
    (dptr dlen cap : UInt64) (hpre : pre.length = dlen.toNat)
    (hcap2 : dlen.toNat + 16 ≤ cap.toNat) (hcap2' : cap.toNat < 2 ^ 63)
    (R0 : DataMem → Prop)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (slot.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
      ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
      ⋆ Eq (b4.At (s.regs.rbx.toBitVec + 15))
      ⋆ Eq (c0.At s.regs.rax.toBitVec) ⋆ Eq (c1.At (s.regs.rax.toBitVec + 2))
      ⋆ Eq (c2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (c3.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq (c4.At (s.regs.rax.toBitVec + 16))
      ⋆ (Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (sp1.At (s.regs.rsp.toBitVec + 8))
        ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
        ⋆ Eq (pre.At dptr.toBitVec) ⋆ Eq (d0.At (dptr.toBitVec + dlen.toBitVec))
        ⋆ Eq (d1.At (dptr.toBitVec + dlen.toBitVec + 1)) ⋆ Eq (d2.At (dptr.toBitVec + dlen.toBitVec + 3))
        ⋆ Eq (d3.At (dptr.toBitVec + dlen.toBitVec + 7)) ⋆ Eq (d4.At (dptr.toBitVec + dlen.toBitVec + 15)) ⋆ R0))
    (hL37f : ∀ i < kd, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_37"))
    (hL3bf : ∀ i < kd, Host.prog[i]? ≠ some (.label "L_target.Scalars.UnmarshalSSZ_3b"))
    (hlen : s.regs.rcx = 16) (hb4 : b4 = [0] ∨ b4 = [1]) (hguard : guard.toNat < s.regs.rsp.toNat) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = 0 ∧
        ∀ (m2 : DataMem) (zm : RegZmms) (fl : StatusFlags),
          (∀ F : DataMem → Prop, (Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) st.data.dmem →
            (Eq ((Int.toBytes 8 ra2.toBitVec.toInt).At s.regs.rsp.toBitVec) ⋆ F) m2) →
          Eventually (step1 Host.exe)
            (fun st' => st'.pc = Int64.ofBitVec ra2.toBitVec ∧ st'.data.regs.rax = dptr
              ∧ st'.data.regs.rbx = dlen + 16 ∧
              (Eq (b0.At (dptr.toBitVec + dlen.toBitVec)) ⋆ Eq (b1.At (dptr.toBitVec + dlen.toBitVec + 1))
                ⋆ Eq (b2.At (dptr.toBitVec + dlen.toBitVec + 3)) ⋆ Eq (b3.At (dptr.toBitVec + dlen.toBitVec + 7))
                ⋆ Eq (b4.At (dptr.toBitVec + dlen.toBitVec + 15)) ⋆ Eq (pre.At dptr.toBitVec)
                ⋆ Eq (b0.At s.regs.rax.toBitVec) ⋆ Eq (b1.At (s.regs.rax.toBitVec + 2))
                ⋆ Eq (b2.At (s.regs.rax.toBitVec + 4)) ⋆ Eq (b3.At (s.regs.rax.toBitVec + 8))
                ⋆ Eq (b4.At (s.regs.rax.toBitVec + 16))
                ⋆ Eq (b0.At s.regs.rbx.toBitVec) ⋆ Eq (b1.At (s.regs.rbx.toBitVec + 1))
                ⋆ Eq (b2.At (s.regs.rbx.toBitVec + 3)) ⋆ Eq (b3.At (s.regs.rbx.toBitVec + 7))
                ⋆ Eq (b4.At (s.regs.rbx.toBitVec + 15)) ⋆ R0 ⋆ fun _ => True) st'.data.dmem)
            ⟨⟨{ st.data.regs with rax := s.regs.rax, rbx := dptr, rcx := dlen, rdi := cap, rsp := s.regs.rsp },
              zm, fl, m2⟩, Host.addrOf km⟩)
      ⟨s, Host.addrOf kd⟩ := by
  refine eventually_trans _ _ _ _ (sc_accept_main kd hkd s ra slot b0 b1 b2 b3 b4 c0 c1 c2 c3 c4 hsl h0l h1l h2l h3l h4l
    g0 g1 g2 g3 g4 _ h_mem hL37f hL3bf hlen hb4) ?_
  rintro ⟨d', pc⟩ ⟨hpc, hrax, -, -, hr14, hm⟩
  refine Eventually.done _ ⟨hpc, hrax, fun m2 zm fl hupd => ?_⟩
  have hm2 := hupd _ (by ecancel)
  have hb4' : b4 = [0] ∨ b4 = [1] := hb4
  refine eventually_trans _ _ _ _ (sc_marshal_main km hkm hfm _ ra2 guard fp sp1 (Int.toBytes 8 s.regs.rbx.toBitVec.toInt)
    b0 b1 b2 b3 b4 d0 d1 d2 d3 d4 pre hfp hs1 (Int.toBytes_length 8 _) h0l h1l h2l h3l hd0 hd1 hd2 hd3 hd4 _
    (by dsimp only; rw [hr14]; ecancel)
    (by dsimp only; exact hguard) (by dsimp only; omega) (by dsimp only; exact hcap2') hb4') ?_
  intro st' hh
  obtain ⟨e1, e2, e3, -, -, -, -, -, -, hm'⟩ := hh
  dsimp only at e2 e3 hm'
  exact Eventually.done _ ⟨e1, e2, e3, sep_true (by ecancel)⟩
