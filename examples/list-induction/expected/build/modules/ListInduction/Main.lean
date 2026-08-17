module
public import Init
set_option autoImplicit false
namespace ListInduction.Main

public theorem nil_append (llv0 : Type) (llv1 : List llv0) : Eq (List.append List.nil llv1) llv1 := by
  rfl

public theorem cons_append (llv0 : Type) (llv1 : llv0) (llv2 : List llv0) (llv3 : List llv0) : Eq (List.append (List.cons llv1 llv2) llv3) (List.cons llv1 (List.append llv2 llv3)) := by
  rfl

public theorem length_singleton (llv0 : Type) (llv1 : llv0) : Eq (List.length (List.cons llv1 List.nil)) (1 : Nat) := by
  rfl

public theorem length_cons (llv0 : Type) (llv1 : llv0) (llv2 : List llv0) : Eq (List.length (List.cons llv1 llv2)) (Nat.succ (List.length llv2)) := by
  rfl

public theorem append_nil (llv0 : Type) (llv1 : List llv0) : Eq (List.append llv1 List.nil) llv1 := by
  induction llv1 with
    | nil =>
      rfl
    | cons llh0 llh1 llh2 =>
      rw [ListInduction.Main.cons_append llv0 llh0 llh1 List.nil, llh2]

public theorem succ_add_doc (llv0 : Nat) (llv1 : Nat) : Eq (Nat.add (Nat.succ llv0) llv1) (Nat.succ (Nat.add llv0 llv1)) := by
  exact Nat.succ_add llv0 llv1

public theorem length_append (llv0 : Type) (llv1 : List llv0) (llv2 : List llv0) : Eq (List.length (List.append llv1 llv2)) (Nat.add (List.length llv1) (List.length llv2)) := by
  exact List.length_append

end ListInduction.Main
