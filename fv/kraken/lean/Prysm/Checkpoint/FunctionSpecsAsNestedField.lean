import Prysm.Checkpoint.DecodeAccept
import Prysm.Checkpoint.EncodeFastPath
import Prysm.AttestationData.Code
import Runtime.CopyModel

/-!
# Function specifications of the Checkpoint decoder and encoder

`Decode.accept_function_spec Heap S` is the statement of `Prysm.Checkpoint.Decode.accept` as a hypothesis-shaped property of
the code at the label `(*Checkpoint).UnmarshalSSZ` (the form of `Prysm.Epoch.Decode.accept_function_spec`): for
every machine state, return address and frame `F`. The only change to the statement is that the
callee's own `makeslice` return-slot word at rsp − 96 (`Host.addrOf (k + 70)` in the theorem) is an
existential `rs'` of 8 bytes, so that the specification does not name the callee's place.
`Decode.accept_function_spec_holds` proves it from the machine code (`Prysm.Checkpoint.Decode.accept`, with `Prysm.Epoch.Decode.accept_function_spec_holds`
inside); the runtime contracts the callee needs (`MakesliceContract Heap uint8 1 S`, `MemmoveContract S`) are
hypotheses of `Decode.accept_function_spec_holds`, so they stay visible in every caller's statement. Nothing new is
assumed. `Encode.fast_path_function_spec` (encoder) follows the same rule (below).
-/

open Machine Runtime Prysm.Checkpoint.Code
variable [Host]

namespace Prysm.Checkpoint

def Decode.accept_function_spec (Heap : Nat → DataMem → Prop) (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (avail : Nat)
    (e8 root fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl scratch : List UInt8)
    (F : DataMem → Prop),
    e8.length = 8 → root.length = 32 → fp.length = 8 → s1.length = 8 → s2.length = 8 → l20.length = 8 →
    l28.length = 8 → l30.length = 8 → m0.length = 8 → m1.length = 8 → m2.length = 8 → rslot.length = 8 →
    cst.length = 8 → c0.length = 8 → cP.length = 8 → cL.length = 8 → cC.length = 8 → ctl.length = 32 →
    8 ≤ S → S < 2 ^ 60 → scratch.length = S →
    guard.toNat + 96 < st.regs.rsp.toNat → st.regs.rcx = 40 → 32 ≤ avail →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s1.At (st.regs.rsp.toBitVec + 8))
      ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq (l20.At (st.regs.rsp.toBitVec - 32)) ⋆ Eq (l28.At (st.regs.rsp.toBitVec - 40))
      ⋆ Eq (l30.At (st.regs.rsp.toBitVec - 48))
      ⋆ Eq (m2.At (st.regs.rsp.toBitVec - 72)) ⋆ Eq (m1.At (st.regs.rsp.toBitVec - 80))
      ⋆ Eq (m0.At (st.regs.rsp.toBitVec - 88)) ⋆ Eq (rslot.At (st.regs.rsp.toBitVec - 96))
      ⋆ Eq (scratch.At (st.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Heap avail
      ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (root.At (st.regs.rbx.toBitVec + 8))
      ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (c0.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq (cP.At (st.regs.rax.toBitVec + 16)) ⋆ Eq (cL.At (st.regs.rax.toBitVec + 24))
      ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32)) ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40))
      ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = 0 ∧ st'.data.regs.rbx = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (p : BitVec 64) (scr mm rs' : List UInt8), scr.length = S ∧ mm.length = 24 ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rax.toBitVec.toInt).At (st.regs.rsp.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rsp.toBitVec - 32))
          ⋆ Eq ((Int.toBytes 8 0).At (st.regs.rsp.toBitVec - 40))
          ⋆ Eq ((Int.toBytes 8 0).At (st.regs.rsp.toBitVec - 48))
          ⋆ Eq (mm.At (st.regs.rsp.toBitVec - 88))
          ⋆ Eq (rs'.At (st.regs.rsp.toBitVec - 96))
          ⋆ Eq (scr.At (st.regs.rsp.toBitVec - 96 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Heap (avail - 32)
          ⋆ Eq (e8.At st.regs.rbx.toBitVec) ⋆ Eq (root.At (st.regs.rbx.toBitVec + 8))
          ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq ([0, 0, 0, 0].At (label "runtime.writeBarrier").toBitVec) ⋆ F) st'.data.dmem)
      ⟨st, label Prysm.Checkpoint.Code.unmarshalSSZLabel⟩

theorem Decode.accept_function_spec_holds (k : Nat) (hk : unmarshalSSZ.IsInfixAt Host.prog k) (hf : LabelsFresh unmarshalSSZ k)
    (kE : Nat) (hkE : Prysm.Epoch.Code.unmarshalSSZ.IsInfixAt Host.prog kE) (hfE : LabelsFresh Prysm.Epoch.Code.unmarshalSSZ kE)
    (Heap : Nat → DataMem → Prop) (S : Nat)
    (hms : MakesliceContract Heap ElfData.PrysmTarget.typeUint8_addr 1 S) (hmm : MemmoveContract S) : Decode.accept_function_spec Heap S := by
  intro st ret guard avail e8 root fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl scratch F
    he8 hroot hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0 hcP hcL hcC hctl hS8 hS hsc hguard hlen hav hm
  rw [show label Prysm.Checkpoint.Code.unmarshalSSZLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  refine eventually_mono (Prysm.Checkpoint.Decode.accept k hk hf kE hkE hfE e8 root he8 hroot st (UInt64.ofBitVec ret.toBitVec)
    guard fp s1 s2 l20 l28 l30 m0 m1 m2 rslot cst c0 cP cL cC ctl hfp h1 h2 hl20 hl28 hl30 hm0 hm1 hm2 hrs hcst hc0
    hcP hcL hcC hctl F S hS8 hS scratch hsc Heap avail hm hguard hlen hav hms hmm) ?_
  rintro st' ⟨h1, h2, h3, h4, h5, h6, p, scr, mm, hscr, hmm', hmem⟩
  exact ⟨h1, h2, h3, h4, h5, h6, p, scr, mm, _, hscr, hmm', Int.toBytes_length 8 _, hmem⟩

/-- **Function specification of `(*Checkpoint).MarshalSSZTo`, fast path** (capacity for 40 more bytes,
`len(Root) = 32`): the statement of `Prysm.Checkpoint.Encode.fast_path` at the label, for every state, return
address and frame; the callee's return-slot word at rsp − 120 (`Host.addrOf (k + 63)`) is an
existential `rs'`. `Encode.fast_path_function_spec_holds` proves it; `MemmoveContract S` is its hypothesis. -/
def Encode.fast_path_function_spec (S : Nat) : Prop :=
  ∀ (st : MachineData) (ret : Int64) (guard : UInt64) (p : BitVec 64)
    (cst e8 cC ctl root pre d0 d1 fp s2 l16 l24 l32 t40 t30 rslot scratch : List UInt8) (F : DataMem → Prop),
    cst.length = 8 → e8.length = 8 → cC.length = 8 → ctl.length = 32 → root.length = 32 → d0.length = 8 →
    d1.length = 32 → pre.length = st.regs.rcx.toNat → fp.length = 8 → s2.length = 8 → l16.length = 8 →
    l24.length = 8 → l32.length = 8 → t40.length = 16 → t30.length = 16 → rslot.length = 8 → scratch.length = S →
    guard.toNat < st.regs.rsp.toNat → 120 ≤ st.regs.rsp.toNat →
    st.regs.rcx.toNat + 40 ≤ st.regs.rdi.toNat → st.regs.rdi.toNat < 2 ^ 63 →
    (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
      ⋆ Eq (fp.At (st.regs.rsp.toBitVec - 8)) ⋆ Eq (s2.At (st.regs.rsp.toBitVec + 16))
      ⋆ Eq (l16.At (st.regs.rsp.toBitVec - 16)) ⋆ Eq (l24.At (st.regs.rsp.toBitVec - 24))
      ⋆ Eq (l32.At (st.regs.rsp.toBitVec - 32)) ⋆ Eq (t30.At (st.regs.rsp.toBitVec - 48))
      ⋆ Eq (t40.At (st.regs.rsp.toBitVec - 64))
      ⋆ Eq (rslot.At (st.regs.rsp.toBitVec - 120)) ⋆ Eq (scratch.At (st.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
      ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
      ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
      ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
      ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32))
      ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
      ⋆ Eq (pre.At st.regs.rbx.toBitVec) ⋆ Eq (d0.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec))
      ⋆ Eq (d1.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec + 8)) ⋆ F) st.dmem →
    Eventually (step1 Host.exe)
      (fun st' => st'.pc = ret ∧ st'.data.regs.rax = st.regs.rbx
        ∧ st'.data.regs.rbx.toNat = st.regs.rcx.toNat + 40 ∧ st'.data.regs.rcx = st.regs.rdi
        ∧ st'.data.regs.rdi = 0 ∧ st'.data.regs.rsi = 0
        ∧ st'.data.regs.rsp = st.regs.rsp + 8 ∧ st'.data.regs.rbp = st.regs.rbp ∧ st'.data.regs.r14 = st.regs.r14 ∧
        ∃ (t u scr rs' : List UInt8), t.length = 8 ∧ u.length = 16 ∧ scr.length = S ∧ rs'.length = 8 ∧
        (Eq ((Int.toBytes 8 ret.toBitVec.toInt).At st.regs.rsp.toBitVec)
          ⋆ Eq ((Int.toBytes 8 st.regs.rbp.toBitVec.toInt).At (st.regs.rsp.toBitVec - 8))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 st.regs.rbx.toBitVec.toInt).At (st.regs.rsp.toBitVec - 16))
          ⋆ Eq ((Int.toBytes 8 st.regs.rdi.toBitVec.toInt).At (st.regs.rsp.toBitVec - 24))
          ⋆ Eq ((Int.toBytes 8 (st.regs.rcx.toBitVec + 40).toInt).At (st.regs.rsp.toBitVec - 32))
          ⋆ Eq (u.At (st.regs.rsp.toBitVec - 48)) ⋆ Eq (e8.At (st.regs.rsp.toBitVec - 64))
          ⋆ Eq (t.At (st.regs.rsp.toBitVec - 56))
          ⋆ Eq (rs'.At (st.regs.rsp.toBitVec - 120))
          ⋆ Eq (scr.At (st.regs.rsp.toBitVec - 120 - BitVec.ofNat 64 S))
          ⋆ Eq ((Int.toBytes 8 guard.toBitVec.toInt).At (st.regs.r14.toBitVec + 16))
          ⋆ Eq (cst.At st.regs.rax.toBitVec) ⋆ Eq (e8.At (st.regs.rax.toBitVec + 8))
          ⋆ Eq ((Int.toBytes 8 p.toInt).At (st.regs.rax.toBitVec + 16))
          ⋆ Eq ((Int.toBytes 8 32).At (st.regs.rax.toBitVec + 24)) ⋆ Eq (cC.At (st.regs.rax.toBitVec + 32))
          ⋆ Eq (ctl.At (st.regs.rax.toBitVec + 40)) ⋆ Eq (root.At p)
          ⋆ Eq (pre.At st.regs.rbx.toBitVec) ⋆ Eq (e8.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec))
          ⋆ Eq (root.At (st.regs.rbx.toBitVec + st.regs.rcx.toBitVec + 8)) ⋆ F) st'.data.dmem)
      ⟨st, label Prysm.Checkpoint.Code.marshalSSZToLabel⟩

theorem Encode.fast_path_function_spec_holds (k : Nat) (hk : marshalSSZTo.IsInfixAt Host.prog k) (hf : LabelsFresh marshalSSZTo k)
    (S : Nat) (hmm : MemmoveContract S) : Encode.fast_path_function_spec S := by
  intro st ret guard p cst e8 cC ctl root pre d0 d1 fp s2 l16 l24 l32 t40 t30 rslot scratch F
    hcst he8 hcC hctl hroot hd0 hd1 hpre hfp h2 hl16 hl24 hl32 ht40 ht30 hrs hsc hguard hsp hcap hcap63 hm
  rw [show label Prysm.Checkpoint.Code.marshalSSZToLabel = Host.addrOf (k + 0) from label_at hk hf (j := 0) (by rfl) (by intro i hi; omega)]
  refine eventually_mono (Prysm.Checkpoint.Encode.fast_path k hk hf cst e8 cC ctl root pre d0 d1 hcst he8 hcC hctl hroot hd0 hd1
    p st (UInt64.ofBitVec ret.toBitVec) guard hpre fp s2 l16 l24 l32 t40 t30 rslot hfp h2 hl16 hl24 hl32 ht40 ht30 hrs
    F S scratch hsc hm hguard hsp hcap hcap63 hmm) ?_
  rintro st' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, t, u, scr, ht, hu, hscr, hmem⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, t, u, scr, _, ht, hu, hscr, Int.toBytes_length 8 _, hmem⟩

end Prysm.Checkpoint
