module
public import Init
public import SemanticFixture.KernelReductionDefinitions
set_option autoImplicit false
namespace SemanticFixture.KernelReductionProofs

public theorem importedAppendLengthIsFour : (SemanticFixture.KernelReductionDefinitions.importedLength = 4) := by
  decide

end SemanticFixture.KernelReductionProofs
