import Lean
namespace EscapeNegative
axiom injected : False
theorem publicFalse : False := by sorry
private theorem privateFalse : False := by sorry
def retainedFalse : False := privateFalse
theorem fromCustom : False := injected
end EscapeNegative
