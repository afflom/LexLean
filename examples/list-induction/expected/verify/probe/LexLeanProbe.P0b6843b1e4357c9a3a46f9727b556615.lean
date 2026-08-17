module
import Init
set_option autoImplicit false
universe p0u p1u p2u p3u p4u p5u p6u
example : {x0 : Type p0u} → (x1 : List x0) → (x2 : List x0) → List x0 := List.append
example : {x0 : Type p1u} → (x1 : x0) → (x2 : List x0) → List x0 := List.cons
example : {x0 : Type p2u} → (x1 : List x0) → Nat := List.length
example : {x0 : Type p3u} → (x1 : List x0) → Nat := List.length
example : {x0 : Type p4u} → {x1 : List x0} → {x2 : List x0} → Eq (List.length (List.append x1 x2)) (Nat.add (List.length x1) (List.length x2)) := List.length_append
example : (x0 : Type p5u) → Type p5u := List
example : {x0 : Type p6u} → List x0 := List.nil
example : (x0 : Nat) → (x1 : Nat) → Eq (Nat.add (Nat.succ x0) x1) (Nat.succ (Nat.add x0 x1)) := Nat.succ_add
example : (x0 : Nat) → (x1 : Nat) → Nat := Nat.add
example : (x0 : Nat) → (x1 : Nat) → Nat := Nat.add
example : Type := Nat
example : (x0 : Nat) → Nat := Nat.succ
