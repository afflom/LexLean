module
public import Init
public import UorAtlas.Blocks
set_option autoImplicit false
namespace LexLeanExample.Main

public theorem dimension_is_fixed (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

public theorem support_is_a_function (llv0 : UorAtlas.Blocks.D17) : Eq (UorAtlas.Blocks.D17a llv0) (UorAtlas.Blocks.D17a llv0) := by
  rfl

public theorem presentation_is_a_type (llv0 : UorAtlas.Blocks.D17) : Eq llv0 llv0 := by
  rfl

public theorem add_successor (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add llv0 (Nat.add llv1 1)) (Nat.add (Nat.add llv0 llv1) 1) := by
  rfl

public theorem root_count_is_a_constant (llv0 : Nat) : Eq (Nat.add 0 llv0) llv0 := by
  induction llv0 with
    | zero =>
      rfl
    | succ llh0 llh1 =>
      rw [LexLeanExample.Main.add_successor (0 : Nat) llh0, llh1]

end LexLeanExample.Main
