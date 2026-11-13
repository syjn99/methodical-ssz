import Codec.SegmentTemplate
import Machine.Step

/-!
# GEN4 L1: a code view that skips padding `nop` directives (variation class V1)

The hold-outs H4 and H5 missed fields because Go 1.26.10 put a one-byte `nop` inside a known shape (before
`callq runtime.makeslice`, after a callee `callq`, at the end of an argument set-up). GEN3 answered with one
`pad` flag per observed position. This module gives ONE mechanism for every position.

* `isNop d`: `d` is a `nop` instruction. `eraseNop q`: `q` without its nops. `nopPos q i`: the index in `q` of
  the i-th directive that is not a nop (`q.length` after the last one, `nopPos_len`).
* A G4 lemma takes a WINDOW of the host program instead of a dense template:
  `(hq : q.IsInfixAt Host.prog j) (he : eraseNop q = tmpl …) (hend : j + q.length = e)`.
  The window may hold nops before, between and after the template directives; there is no pad flag and no
  position parameter. An instance takes `q := (C.drop a).take n` (`win`) and proves `he` by computation.
* Stepping: `wat` (template directive `i` is at `j + nopPos q i`), `wskip0` (leading nops), `wskip` (nops
  between directive `i` and `i + 1`), `wlast` (nops after the last directive), `wnops` (a window of nops only).
  Tactics `kwin`, `kwat`, `kwnx`, `kwend` are the window forms of `kat` (`Machine/Step.lean`).

Why the dense lemmas are not transferred by a general theorem: a `callq` pushes the address of the NEXT
directive. In the real program that is the address of the nop, in a nop-erased program the address of the
instruction after it; the two machine states differ. The window lemmas are therefore proved directly (the
proof texts of the dense lemmas with `kwat` for `kat`), and the dense lemmas are their `q := tmpl` instances.
Nothing here is trusted beyond `Machine.Step`.
-/

open Machine

namespace Codec

/-- A padding directive: the `nop` instruction (any length field). -/
def isNop : Directive → Bool
  | Kraken.Directive.instr (Instr.regular _ _ (Operation.nop _)) => true
  | _ => false
/-- `q` without its `nop` directives. -/
def eraseNop (q : Program) : Program := q.filter (fun d => !isNop d)
/-- Index in `q` of the i-th directive that is not a `nop`; `q.length` if there are fewer. -/
def nopPos : Program → Nat → Nat
  | [], _ => 0
  | d :: q, i => if isNop d then nopPos q i + 1 else
      match i with
      | 0 => 0
      | i' + 1 => nopPos q i' + 1
/-- The first directive of a list, as a list (`[]` for `[]`). -/
def hd1 : Program → Program
  | [] => []
  | d :: _ => [d]

theorem nopPos_cons_nop {a : Directive} {q : Program} (i : Nat) (h : isNop a = true) :
    nopPos (a :: q) i = nopPos q i + 1 := by simp [nopPos, h]
theorem nopPos_cons_zero {a : Directive} {q : Program} (h : isNop a = false) : nopPos (a :: q) 0 = 0 := by
  simp [nopPos, h]
theorem nopPos_cons_succ {a : Directive} {q : Program} (i : Nat) (h : isNop a = false) :
    nopPos (a :: q) (i + 1) = nopPos q i + 1 := by simp [nopPos, h]
theorem eraseNop_cons_nop {a : Directive} {q : Program} (h : isNop a = true) : eraseNop (a :: q) = eraseNop q := by
  simp [eraseNop, h]
theorem eraseNop_cons {a : Directive} {q : Program} (h : isNop a = false) :
    eraseNop (a :: q) = a :: eraseNop q := by simp [eraseNop, h]

theorem nil_infix {α : Type} (l : List α) (k : Nat) : ([] : List α).IsInfixAt l k := by
  rw [List.isInfixAt_iff_getElem?]
  intro i hi
  exact absurd hi (Nat.not_lt_zero _)
theorem infix_head {α : Type} {d : α} {q l : List α} {j : Nat} (h : (d :: q).IsInfixAt l j) : [d].IsInfixAt l j :=
  Codec.infix_sub (q := [d]) 0 h rfl
theorem infix_tail {α : Type} {d : α} {q l : List α} {j : Nat} (h : (d :: q).IsInfixAt l j) : q.IsInfixAt l (j + 1) :=
  Machine.isInfixAt_drop h 1
/-- The window `(p.drop a).take n` of a fragment `p` at `k` is at `k + a`. -/
theorem win {α : Type} {p l : List α} {k : Nat} (h : p.IsInfixAt l k) (a n : Nat) :
    ((p.drop a).take n).IsInfixAt l (k + a) := by
  have h1 := Machine.isInfixAt_drop h a
  rw [List.isInfixAt_iff_getElem?] at *
  intro i hi
  simp only [List.length_take] at hi
  rw [h1 i (by omega), List.getElem_take]


variable [Host]

theorem ev_pc {final : MachineState → Prop} {s : MachineData} {a b : Nat} (h : a = b)
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf a⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf b⟩ := h ▸ hk

/-- One `nop` directive is a step that changes nothing. -/
theorem nop_step {d : Directive} {j : Nat} (hd : [d].IsInfixAt Host.prog j) (hn : isNop d = true)
    {final : MachineState → Prop} {s : MachineData}
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + 1)⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  unfold isNop at hn
  split at hn
  · apply Machine.estep hd
    kunfold
    exact hk
  · exact absurd hn (by decide)

/-- The leading nops of a window. -/
theorem wskip0 : ∀ (q : Program) (j : Nat), q.IsInfixAt Host.prog j →
    ∀ {final : MachineState → Prop} {s : MachineData},
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q 0)⟩ →
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  intro q
  induction q with
  | nil => intro j _ final s hk; exact hk
  | cons a q ih =>
    intro j hq final s hk
    cases hn : isNop a
    · rw [nopPos_cons_zero hn] at hk; exact hk
    · rw [nopPos_cons_nop _ hn] at hk
      exact nop_step (infix_head hq) hn (ih (j + 1) (infix_tail hq) (ev_pc (by omega) hk))

theorem wat_aux : ∀ (q : Program) (j i : Nat), q.IsInfixAt Host.prog j →
    (hd1 ((eraseNop q).drop i)).IsInfixAt Host.prog (j + nopPos q i) := by
  intro q
  induction q with
  | nil => intro j i _; cases i <;> exact nil_infix _ _
  | cons a q ih =>
    intro j i hq
    cases hn : isNop a
    · rw [eraseNop_cons hn]
      cases i with
      | zero => rw [nopPos_cons_zero hn]; exact infix_head hq
      | succ i =>
        rw [nopPos_cons_succ _ hn, show j + (nopPos q i + 1) = j + 1 + nopPos q i by omega]
        exact ih (j + 1) i (infix_tail hq)
    · rw [eraseNop_cons_nop hn, nopPos_cons_nop _ hn, show j + (nopPos q i + 1) = j + 1 + nopPos q i by omega]
      exact ih (j + 1) i (infix_tail hq)

theorem wskip_aux : ∀ (q : Program) (j i : Nat), q.IsInfixAt Host.prog j → i < (eraseNop q).length →
    ∀ {final : MachineState → Prop} {s : MachineData},
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q (i + 1))⟩ →
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q i + 1)⟩ := by
  intro q
  induction q with
  | nil => intro j i _ hi; exact absurd hi (Nat.not_lt_zero _)
  | cons a q ih =>
    intro j i hq hi final s hk
    cases hn : isNop a
    · rw [eraseNop_cons hn] at hi
      cases i with
      | zero =>
        rw [nopPos_cons_succ _ hn] at hk
        rw [nopPos_cons_zero hn]
        exact wskip0 q (j + 1) (infix_tail hq) (ev_pc (by omega) hk)
      | succ i =>
        rw [nopPos_cons_succ _ hn] at hk ⊢
        exact ev_pc (by omega) (ih (j + 1) i (infix_tail hq) (Nat.lt_of_succ_lt_succ hi) (ev_pc (by omega) hk))
    · rw [eraseNop_cons_nop hn] at hi
      rw [nopPos_cons_nop _ hn] at hk ⊢
      exact ev_pc (by omega) (ih (j + 1) i (infix_tail hq) hi (ev_pc (by omega) hk))

theorem nopPos_len : ∀ (q : Program), nopPos q (eraseNop q).length = q.length := by
  intro q
  induction q with
  | nil => rfl
  | cons a q ih =>
    cases hn : isNop a
    · rw [eraseNop_cons hn, List.length_cons, nopPos_cons_succ _ hn, ih, List.length_cons]
    · rw [eraseNop_cons_nop hn, nopPos_cons_nop _ hn, ih, List.length_cons]

/-- Directive `i` of the nop-erased window is at `j + nopPos q i` (as a one-element fragment). -/
theorem wat {q t : Program} {j : Nat} (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = t) (i : Nat) :
    (hd1 (t.drop i)).IsInfixAt Host.prog (j + nopPos q i) := he ▸ wat_aux q j i hq
/-- The nops between directive `i` and directive `i + 1` of the window (`hi` by `rfl`). -/
theorem wskip {q t : Program} {j : Nat} (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = t) (i : Nat)
    (hi : Nat.blt i t.length = true) {final : MachineState → Prop} {s : MachineData}
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q (i + 1))⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q i + 1)⟩ :=
  wskip_aux q j i hq (by subst he; exact Nat.le_of_ble_eq_true hi) hk
/-- The nops after the last directive `i` of the window: the pc reaches the window end `e`. -/
theorem wlast {q t : Program} {j : Nat} (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = t) (i : Nat)
    (hi : i + 1 = t.length) {e : Nat} (hend : j + q.length = e) {final : MachineState → Prop} {s : MachineData}
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf (j + nopPos q i + 1)⟩ := by
  subst he hend
  refine wskip_aux q j i hq (by omega) (ev_pc ?_ hk)
  rw [hi, nopPos_len]

/-- A window that holds only nops: the pc moves from `j` to the window end `e`. -/
theorem wnops {q : Program} {j e : Nat} (hq : q.IsInfixAt Host.prog j) (he : eraseNop q = [])
    (hend : j + q.length = e) {final : MachineState → Prop} {s : MachineData}
    (hk : Eventually (step1 Host.exe) final ⟨s, Host.addrOf e⟩) :
    Eventually (step1 Host.exe) final ⟨s, Host.addrOf j⟩ := by
  have h0 : nopPos q 0 = q.length := by
    have := nopPos_len q
    rw [he] at this
    exact this
  exact wskip0 q j hq (ev_pc (by omega) hk)

end Codec

/-- Window form of `kat`: step directive `n` of the template `prog`; the pc is at `j + nopPos q n`. -/
macro "kwat " hq:term:max he:term:max prog:ident n:num : tactic => `(tactic| (
  have hkat := Codec.wat $hq $he $n
  simp only [$prog:ident, Codec.hd1, List.drop_succ_cons, List.drop_zero] at hkat
  apply Machine.estep hkat
  clear hkat
  kunfold))

/-- Skip the leading nops of a window: the pc moves from `j` to `j + nopPos q 0`. -/
macro "kwin " hq:term:max : tactic => `(tactic| refine Codec.wskip0 _ _ $hq ?_)

/-- Skip the nops after directive `n`: the pc moves from `j + nopPos q n + 1` to `j + nopPos q (n + 1)`. -/
macro "kwnx " hq:term:max he:term:max n:num : tactic => `(tactic| refine Codec.wskip $hq $he $n rfl ?_)

/-- Skip the nops after the last directive `n`: the pc moves from `j + nopPos q n + 1` to the window end. -/
macro "kwend " hq:term:max he:term:max n:num hend:term:max : tactic =>
  `(tactic| refine Codec.wlast $hq $he $n rfl $hend ?_)
