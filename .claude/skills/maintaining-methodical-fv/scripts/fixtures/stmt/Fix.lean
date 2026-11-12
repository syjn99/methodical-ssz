-- decl_drift fixture: theorem statement changed.
namespace Fix

private def helper (n : Nat) : Nat := n + 1

def pub (n : Nat) : Nat := helper n

theorem pub_pos (n : Nat) : 0 < pub n := by
  unfold pub helper; omega

theorem stmt (n : Nat) : 0 + n = n := Nat.zero_add n

theorem em_dec (p : Prop) [Decidable p] : p ∨ ¬p := Decidable.em p

def gone : Nat := 3

end Fix
