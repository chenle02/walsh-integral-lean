import Lean
namespace EscapeNative
theorem nativeTrue : (2 : Nat) + 2 = 4 := by native_decide
end EscapeNative
