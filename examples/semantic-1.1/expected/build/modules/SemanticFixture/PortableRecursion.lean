module
public import Init
set_option autoImplicit false
namespace SemanticFixture.PortableRecursion

public inductive PortableOptionByte where
  | none
  | some (_ : UInt8)

public inductive PortableResultByte where
  | error (_ : String)
  | ok (_ : UInt8)

@[expose] public def byteListLength : (bytes : List (UInt8)) -> Nat
  | List.nil => 0
  | List.cons _ tail => (1 + byteListLength (tail))

@[expose] public def echoBytes : (bytes : List (UInt8)) -> List (UInt8)
  | List.nil => ([] : List (UInt8))
  | List.cons head tail => (head :: echoBytes (tail))

@[expose] public def optionIsSome : (value : PortableOptionByte) -> Bool
  | PortableOptionByte.none => false
  | PortableOptionByte.some _ => true

@[expose] public def resultIsOk : (value : PortableResultByte) -> Bool
  | PortableResultByte.error _ => false
  | PortableResultByte.ok _ => true

@[expose] public def builtinOptionSome : Option (UInt8) := Option.some ((7 : UInt8))

@[expose] public def builtinOptionNone : Option (UInt8) := Option.none

@[expose] public def builtinOptionIsSome (value : Option (UInt8)) : Bool := (match value with | Option.none => false | Option.some _ => true)

@[expose] public def builtinResultOk : Except (String) (UInt8) := Except.ok ((9 : UInt8))

@[expose] public def builtinResultError : Except (String) (UInt8) := Except.error ("failed")

@[expose] public def builtinResultIsOk (value : Except (String) (UInt8)) : Bool := (match value with | Except.error _ => false | Except.ok _ => true)

end SemanticFixture.PortableRecursion
