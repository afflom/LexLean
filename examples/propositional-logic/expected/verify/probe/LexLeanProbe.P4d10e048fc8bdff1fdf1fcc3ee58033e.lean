module
import Init
set_option autoImplicit false
universe p0u
example : {x0 : Prop} → {x1 : Type p0u} → (x2 : x0) → (x3 : Not x0) → x1 := absurd
example : (x0 : Prop) → Or x0 (Not x0) := Classical.em
example : {x0 : Prop} → {x1 : Prop} → (x2 : x0) → (x3 : x1) → And x0 x1 := And.intro
example : {x0 : Prop} → {x1 : Prop} → (x3 : (x2 : x0) → x1) → (x5 : (x4 : x1) → x0) → Iff x0 x1 := Iff.intro
example : {x0 : Prop} → {x1 : Prop} → (x2 : x0) → Or x0 x1 := Or.inl
example : {x0 : Prop} → {x1 : Prop} → (x2 : x1) → Or x0 x1 := Or.inr
