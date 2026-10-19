import Lean
namespace EscapePositive
theorem publicTrue : True := True.intro
private theorem privateTrue : True := True.intro
def retainedTrue : True := privateTrue
end EscapePositive
