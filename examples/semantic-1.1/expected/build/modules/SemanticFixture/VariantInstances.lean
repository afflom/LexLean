module
public import Init
public import SemanticFixture.VariantTypes
set_option autoImplicit false
namespace SemanticFixture.VariantInstances

public class UsesDefault (A : Type) where
  inner : SemanticFixture.VariantTypes.DefaultValue (A)

public instance (priority := 1000) natUsesDefault : UsesDefault (Nat) where
  inner := SemanticFixture.VariantTypes.natDefault

end SemanticFixture.VariantInstances
