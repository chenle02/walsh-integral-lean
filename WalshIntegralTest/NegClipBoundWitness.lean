import WalshIntegral

open WalshIntegral.Modification

namespace WalshIntegralTest.NegClipBound

theorem clip_bound : |clipField 2 (fun _ _ (_ : Unit) => 2) 0 0 ()| ≤ (2 : ℝ) :=
  clipField_abs_le 2 (fun _ _ (_ : Unit) => 2) 0 0 ()

theorem clip_value : |clipField 2 (fun _ _ (_ : Unit) => 2) 0 0 ()| = (2 : ℝ) := by
  norm_num [clipField]

theorem smaller_bound : (2 : ℝ) - 1 = 1 := by
  norm_num

end WalshIntegralTest.NegClipBound
