/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.LongChainMonotonicity

/-!
# Four sites: the first unsaturated chain

The uncertainty ratio `C` of the maximal current state saturates at `N = 2, 3` (Physlib #1718),
grows strictly from `N = 4` on (#1735) and tends to `√(π²/3 − 2)` (#1734). Four sites is the
first unsaturated chain. There `cos (π / 5) = (1 + √5) / 4` gives the exact value of `C²`, and
from there on `C²` stays in one fixed band, uniformly in `N`.

## Main results

- `ProperTimeGR.uncertaintyRatioSqForm_five` : the closed form of `C²` at `n = 5` is
  `(99 − 42 √5) / 5`.
- `ProperTimeGR.uncertaintyRatio_sq_of_N_eq_four` : `C² = (99 − 42 √5) / 5` for `N = 4`.
- `ProperTimeGR.uncertaintyRatio_sq_mem_Ico` : for `N ≥ 4`,
  `C² ∈ [(99 − 42 √5) / 5, π²/3 − 2)`.
-/

@[expose] public noncomputable section

open Set CondensedMatter CondensedMatter.TightBindingChain

namespace ProperTimeGR

/-- At `n = 5` the closed form is `(99 − 42 √5) / 5`, from `cos (π / 5) = (1 + √5) / 4`. -/
theorem uncertaintyRatioSqForm_five : uncertaintyRatioSqForm 5 = (99 - 42 * √5) / 5 := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hs : Real.sin (Real.pi / 5) ^ 2 = (5 - √5) / 8 := by
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / 5), Real.cos_pi_div_five]
  rw [uncertaintyRatioSqForm, Real.sinc_of_ne_zero (by positivity), Real.cos_pi_div_five]
  field_simp
  rw [hs]
  nlinarith

/-- For `N = 4`, `C² = (99 − 42 √5) / 5`. -/
theorem uncertaintyRatio_sq_of_N_eq_four (T : TightBindingChain) (ht : T.t ≠ 0) (hN : T.N = 4) :
    T.uncertaintyRatio ^ 2 = (99 - 42 * √5) / 5 := by
  rw [T.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht (by omega), hN,
    show ((4 : ℕ) : ℝ) + 1 = 5 by norm_num, uncertaintyRatioSqForm_five]

/-- For `N ≥ 4`, `C²` lies in `[(99 − 42 √5) / 5, π²/3 − 2)`, uniformly in `N`. -/
theorem uncertaintyRatio_sq_mem_Ico (T : TightBindingChain) (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.uncertaintyRatio ^ 2 ∈ Ico ((99 - 42 * √5) / 5) (Real.pi ^ 2 / 3 - 2) := by
  have h5 : (5 : ℝ) ≤ T.N + 1 := by
    have : (4 : ℝ) ≤ T.N := by exact_mod_cast hN
    linarith
  refine ⟨?_, ?_⟩
  · rw [T.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht (by omega),
      ← uncertaintyRatioSqForm_five]
    exact uncertaintyRatioSqForm_strictMonoOn.monotoneOn (le_refl (5 : ℝ)) h5 h5
  · rw [← Real.sq_sqrt (show (0 : ℝ) ≤ Real.pi ^ 2 / 3 - 2 by nlinarith [Real.pi_gt_three])]
    exact pow_lt_pow_left₀ (T.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two ht hN)
      (div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) two_ne_zero

end ProperTimeGR
