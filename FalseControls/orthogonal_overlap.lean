import PriceOfDirection.Basic
-- Orthogonal unit directions overlap as cos²θ = 0, not 1: they are fully separated.
example : ((1 : ℝ) * 0 + 0 * 1) ^ 2 = 1 := by norm_num
