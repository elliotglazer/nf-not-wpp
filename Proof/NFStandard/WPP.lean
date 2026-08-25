import SemanticCore.PartialLowering
import WPPCompactSourceSyntax

namespace NFChoice.Foundation.NFStandard

open NFChoice.SemanticCore.PartialLowering
open NFChoice.Compiler.CompactSourceSyntax

/-- The closed intrinsic formula obtained by lowering the accepted WPP source. -/
def WPPSyntax : Sentence :=
  match lowerClosed syn_wwpp with
  | some f => f
  | none => .falsum

/- The accepted nominal WPP source lowers successfully to `WPPSyntax`. -/
set_option maxHeartbeats 5000000 in
theorem lowerClosed_syn_wwpp : lowerClosed syn_wwpp = some WPPSyntax := by
  set_option maxRecDepth 30000 in
    rfl

/-- WPP as a Flypitch sentence, exactly lowered from the accepted source. -/
def WPP : Fol.sentence LNF := Formula.toFlypitch WPPSyntax

#print axioms lowerClosed_syn_wwpp

end NFChoice.Foundation.NFStandard
