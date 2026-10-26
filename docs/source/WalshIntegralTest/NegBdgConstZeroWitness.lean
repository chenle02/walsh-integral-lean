module

public import WalshIntegral

public section

open WalshIntegral.MomentBound

namespace WalshIntegralTest.NegBdgConstZero

theorem gaussian_positive : 0 < gaussianMoment 2 :=
  gaussianMoment_pos (p := 2) (by norm_num)

theorem constant_positive : 0 < bdgConst 2 := by
  have hpositive := gaussian_positive
  unfold bdgConst
  norm_num
  positivity

end WalshIntegralTest.NegBdgConstZero
