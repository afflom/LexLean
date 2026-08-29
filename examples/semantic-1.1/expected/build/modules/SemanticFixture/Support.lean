module
public import Init
set_option autoImplicit false
namespace SemanticFixture.Support

public inductive RemoteFlag where
  | disabled
  | enabled

@[expose] public def remoteEnabled : Bool := true

end SemanticFixture.Support
