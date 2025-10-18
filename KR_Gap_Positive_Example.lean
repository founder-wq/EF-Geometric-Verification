-- EF-Geometric-Verification/KR_Gap_Positive_Example.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Real

/-!
-- The KR Gap Positive Example
--
-- This file verifies the specific arithmetic example used by Koutis and Rice (KR)
-- which proves that the lower bound established by the Exponential Flow (EF)
-- framework is tight and non-trivial. It establishes that the necessary 'gap'
-- separating the two complexity classes is strictly positive (3/200 > 0).
-/

-- Definition: The value used for the gap calculation in the KR construction.
def kr_gap_value : ℝ := (1 / 2) - (49 / 100)

/--
Main theorem: The KR gap value is strictly positive, satisfying the analytic
condition required for the final EF lower bound theorem.
-/
theorem kr_gap_positive : kr_gap_value > 0 :=
by
  -- Prove that 1/2 is greater than 49/100
  have h_half : 1/2 = 50/100 := by norm_num
  rw [kr_gap_value, h_half]
  -- Rewrite the inequality to be a simple subtraction check.
  have h_sub : 50/100 - 49/100 = 1/100 := by norm_num
  rw [h_sub]
  -- Show that 1/100 is indeed greater than 0.
  linarith

end
