-- decl_drift fixture: same as base, comment and layout only.
namespace Fix

private def helper (n : Nat) : Nat := n + 1

def pub (n : Nat) : Nat := helper n

theorem pub_pos (n : Nat) : 0 < pub n := by
  unfold pub helper; omega

theorem stmt (n : Nat) : n + 0 = n := Nat.add_zero n

theorem em_dec (p : Prop) [Decidable p] : p ∨ ¬p := Decidable.em p


-- layout change
def gone : Nat := 3

end Fix
