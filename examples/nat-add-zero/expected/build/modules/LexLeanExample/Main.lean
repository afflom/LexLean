module
import Init
set_option autoImplicit false
namespace LexLeanExample.Main

public theorem add_zero (llv0 : Nat) : Eq (Nat.add llv0 0) llv0 := by
  rfl

end LexLeanExample.Main
