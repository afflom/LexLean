module
import Init
set_option autoImplicit false
universe p1u p12u p19u
example : {x0 : Prop} → {x1 : Prop} → (x2 : x0) → (x3 : x1) → And x0 x1 := And.intro
example : {x0 : Type p1u} → {x2 : (x1 : x0) → Prop} → (x3 : x0) → (x4 : x2 x3) → Exists (fun (x5 : x0) => x2 x5) := Exists.intro
example : (x0 : Nat) → (x1 : Nat) → Nat := Nat.add
example : (x0 : Nat) → (x1 : Nat) → Prop := Nat.le
example : (x0 : Nat) → (x1 : Nat) → Prop := Nat.lt
example : (x0 : Nat) → (x1 : Nat) → Nat := Nat.mul
example : Type := Nat
example : (x0 : Nat) → Nat := Nat.succ
example : Nat := Nat.zero
example : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → Eq (Nat.add (Nat.add x0 x1) x2) (Nat.add x0 (Nat.add x1 x2)) := Nat.add_assoc
example : (x0 : Nat) → (x1 : Nat) → Eq (Nat.add x0 x1) (Nat.add x1 x0) := Nat.add_comm
example : (x0 : Prop) → Or x0 (Not x0) := Classical.em
example : {x0 : Type p12u} → {x1 : x0} → {x2 : x0} → (x3 : Eq x1 x2) → Eq x2 x1 := Eq.symm
example : (x0 : Nat) → Nat.le x0 x0 := Nat.le_refl
example : (x0 : Nat) → Nat.le x0 (Nat.succ x0) := Nat.le_succ
example : {x0 : Nat} → {x1 : Nat} → {x2 : Nat} → (x3 : Nat.le x0 x1) → (x4 : Nat.le x1 x2) → Nat.le x0 x2 := Nat.le_trans
example : (x0 : Nat) → (x1 : Nat) → (x2 : Nat) → Eq (Nat.mul (Nat.mul x0 x1) x2) (Nat.mul x0 (Nat.mul x1 x2)) := Nat.mul_assoc
example : (x0 : Nat) → Eq (Nat.mul x0 (1 : Nat)) x0 := Nat.mul_one
example : (x0 : Nat) → Eq (Nat.mul (1 : Nat) x0) x0 := Nat.one_mul
example : {x0 : Type p19u} → {x1 : x0} → Eq x1 x1 := rfl
example : (x0 : Nat) → (x1 : Nat) → Eq (Nat.add (Nat.succ x0) x1) (Nat.succ (Nat.add x0 x1)) := Nat.succ_add
example : (x0 : Nat) → (fun (x0 : Nat) (x1 : Nat) => Not (Eq x0 x1)) (Nat.succ x0) (0 : Nat) := Nat.succ_ne_zero
example : (x0 : Nat) → Nat := Nat.succ
example : (x0 : Nat) → (x1 : Nat) → Nat := Nat.add
example : (x0 : Nat) → Eq (Nat.mul (2 : Nat) x0) (Nat.add x0 x0) := Nat.two_mul
example : (x0 : Nat) → Eq (Nat.add (0 : Nat) x0) x0 := Nat.zero_add
example : (x0 : Nat) → Nat.lt (0 : Nat) (Nat.succ x0) := Nat.zero_lt_succ
