import E2e.CpMarshal
import E2e.CpSpecK
import Fk.RtCopy

/-!
# Encoder on a decoded-form receiver (NOT the E5 composition)

Review e2e-r1 M1 (FINDINGS R-1): this theorem starts at the encoder entry and
does not run the decoder; it is not `compose_hupd`. The machine-level
composition (decoder entry → `cp_e2e_accept_main` → encoder call) is not done.

`cp_e2e_marshal_decoded_receiver`: the receiver that
`cp_e2e_accept_main` leaves (its postcondition's receiver chunks: `state`
unchanged, `Epoch` = the 8 input bytes `e8`, `Root` = `(p, 32, 32)` with the 32
input bytes `root` at `p`, the tail unchanged) is exactly the receiver premise
of `cp_e2e_marshal_main` (with `Root.cap` = 32). Marshalling it into an empty
`dst` with capacity ≥ 40 returns `(dst[:40], nil)` and `dst[0:40] = e8 ++ root`,
the bytes the decoder read. The full frame accounting of the encoder call is
`cp_e2e_marshal_main`'s conclusion; this corollary states the output bytes
(the rest of memory is the `⋆ True` remainder of that conclusion).

`E2e.WitCpM` runs the encoder on a receiver of this decoded form; there is no
single witness host for decoder and encoder. Spec level: `cp_e2e_spec_roundtrip`.
-/

open Fk E2e.Code EthLib.Serialization.Ssz
variable [Host]

namespace E2e

theorem cpc_add0 (x : BitVec 64) : x + (0 : BitVec 64) = x := BitVec.add_zero x

set_option maxHeartbeats 4000000 in
theorem cp_e2e_marshal_decoded_receiver (km : Nat) (hkm : CpMarshal.IsInfixAt Host.prog km)
    (hfm : LabelsFresh CpMarshal km)
    (cst e8 ctl root d0 d1 : List UInt8) (hcst : cst.length = 8) (he8 : e8.length = 8)
    (hctl : ctl.length = 32) (hroot : root.length = 32) (hd0 : d0.length = 8) (hd1 : d1.length = 32)
    (p : BitVec 64) (s : MachineData) (ra guard : UInt64) (hlen0 : s.regs.rcx = 0)
    (fp s2 l16 l24 l32 t40 t30 rslot : List UInt8)
    (hfp : fp.length = 8) (h2 : s2.length = 8) (hl16 : l16.length = 8) (hl24 : l24.length = 8)
    (hl32 : l32.length = 8) (ht40 : t40.length = 16) (ht30 : t30.length = 16) (hrs : rslot.length = 8)
    (R : DataMem → Prop) (S : Nat) (scratch : List UInt8) (hsc : scratch.length = S)
    (h_mem : s.dmem =⋆ Eq ((Int.toBytes 8 ra.toBitVec.toInt).At s.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (s.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (s.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (s.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (s.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (s.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (s.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (s.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (s.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (s.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (s.regs.r14.toBitVec + 16))
      -- the receiver as cp_e2e_accept_main leaves it
      ⋆ Eq (cst.At s.regs.rax.toBitVec) ⋆ Eq (e8.At (s.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (s.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 24)) ⋆ Eq ((Int.toBytes 8 32).At (s.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (s.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      -- an empty dst with capacity ≥ 40
      ⋆ Eq (d0.At s.regs.rbx.toBitVec) ⋆ Eq (d1.At (s.regs.rbx.toBitVec + 8)) ⋆ R)
    (hguard : guard.toNat < s.regs.rsp.toNat) (hsp : 120 ≤ s.regs.rsp.toNat)
    (hcap : 40 ≤ s.regs.rdi.toNat) (hcap63 : s.regs.rdi.toNat < 2 ^ 63) (hmm : MemmoveC S) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Int64.ofBitVec ra.toBitVec ∧ st.data.regs.rax = s.regs.rbx
        ∧ st.data.regs.rbx.toNat = 40 ∧ st.data.regs.rdi = 0 ∧ st.data.regs.rsi = 0
        ∧ (Eq ((e8 ++ root).At s.regs.rbx.toBitVec) ⋆ fun _ => True) st.data.dmem)
      ⟨s, Host.addrOf km⟩ := by
  have hr0 : s.regs.rcx.toBitVec = 0 := by rw [hlen0]; rfl
  have h := cp_e2e_marshal_main km hkm hfm cst e8 (Int.toBytes 8 32) ctl root [] d0 d1 hcst he8 rfl hctl hroot hd0
    hd1 p s ra guard (by rw [hlen0]; rfl) fp s2 l16 l24 l32 t40 t30 rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs R S
    scratch hsc
    (by simp only [hr0, cpc_add0, errNil_At_emp, Std.ExtHashMap.sep_emp, Std.ExtHashMap.emp_sep]; ecancel)
    hguard hsp (by rw [hlen0]; simpa using hcap) hcap63 hmm
  refine eventually_mono h (fun st ⟨hpc, hrax, hrbx, _, hrdi, hrsi, _, _, _, t, u, scr, _, _, _, hm⟩ =>
    ⟨hpc, hrax, by rw [hrbx, hlen0]; rfl, hrdi, hrsi, ?_⟩)
  rw [hr0, cpc_add0] at hm
  rw [at_app e8 root (b := s.regs.rbx.toBitVec + 8) (by rw [he8]; rfl) (by simp [he8, hroot])]
  exact sep_true (by ecancel)

/-- Spec-level roundtrip: what EthLib decodes, it encodes back to the same bytes. -/
theorem cp_e2e_spec_roundtrip (bs : Array UInt8) (v : Value) (hd : deserialize prysmCpDesc bs = .ok v) :
    serialize prysmCpDesc v = .ok bs := by
  obtain ⟨g, rfl, rfl⟩ := pcp_accepted_is_enc hd
  exact pcp_serialize g

end E2e
