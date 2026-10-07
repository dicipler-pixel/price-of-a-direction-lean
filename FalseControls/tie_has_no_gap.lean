import PriceOfDirection.GapLaw
-- At a tie the overlap is 1/2 however small the coupling: with coupling 1/100 and a unit gap the
-- coupling-over-gap bound would give (1/100)^2/2, and 1/2 is not below that.
example : (1 / 2 : ℝ) ≤ (1 / 100) ^ 2 / 2 := by norm_num
