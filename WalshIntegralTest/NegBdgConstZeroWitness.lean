import WalshIntegral

open WalshIntegral.MomentBound

namespace WalshIntegralTest.NegBdgConstZero

theorem gaussian_positive : 0 < gaussianMoment 2 :=
  gaussianMoment_pos (p := 2) (by norm_num)

theorem constant_positive : 0 < bdgConst 2 := by
  rw [bdgConst_eq]
  norm_num

end WalshIntegralTest.NegBdgConstZero
