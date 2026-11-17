/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime
public import Mathlib.NumberTheory.Niven

/-!
# Niven: the step is never a rational multiple of `1 / |t|` from `N = 3` on

By Niven's theorem (Mathlib `niven_angle_div_pi_eq`), `cos (π / (N + 1))` is rational only for
`N + 1 ∈ {2, 3}`. So `2 |t| τ_pas = 1 / cos (π / (N + 1))` is rational at `N = 2`, and irrational
for every `N ≥ 3`.

## Main results

- `ProperTimeGR.cos_pi_div_succ_irrational` : `cos (π / (N + 1)) ∉ ℚ` for `N ≥ 3`.
- `ProperTimeGR.stepTime_irrational` : `2 |t| τ_pas ∉ ℚ` for `N ≥ 3`.
- `ProperTimeGR.stepTime_two` : at `N = 2`, `2 |t| τ_pas = 2`.
-/

@[expose] public noncomputable section

open Real CondensedMatter

namespace ProperTimeGR

/-- **Niven on the step angle.** `cos (π / (N + 1))` is irrational for `N ≥ 3`. -/
theorem cos_pi_div_succ_irrational {N : ℕ} (hN : 3 ≤ N) :
    ¬ ∃ q : ℚ, Real.cos (π / (N + 1)) = q := by
  rintro ⟨q, hq⟩
  have hN3 : (3 : ℚ) ≤ N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) + 1 := by positivity
  have hr := niven_angle_div_pi_eq (r := 1 / ((N : ℚ) + 1))
    ⟨q, by
      rw [show ((1 / ((N : ℚ) + 1) : ℚ) : ℝ) * π = π / (N + 1) by push_cast; ring]
      exact hq⟩
    ⟨by positivity, by rw [div_le_one hpos]; linarith⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with h | h | h | h | h <;> rw [div_eq_iff hpos.ne'] at h <;> linarith

/-- **The step is irrational in units of `1 / |t|` from `N = 3` on.** -/
theorem stepTime_irrational (T : TightBindingChain) (ht : T.t ≠ 0) (hN : 3 ≤ T.N) :
    ¬ ∃ q : ℚ, 2 * |T.t| * stepTime T = q := by
  rintro ⟨q, hq⟩
  have hc : 0 < Real.cos (π / (T.N + 1)) := cos_pi_div_succ_pos (by omega)
  have hta : 0 < |T.t| := abs_pos.mpr ht
  rw [stepTime_eq] at hq
  have hinv : 1 / Real.cos (π / (T.N + 1)) = q := by
    rw [← hq]
    field_simp
  have hq0 : (q : ℝ) ≠ 0 := by
    rw [← hinv]
    positivity
  apply cos_pi_div_succ_irrational hN
  refine ⟨q⁻¹, ?_⟩
  push_cast
  rw [← hinv, one_div, inv_inv]

/-- At `N = 2` the step is rational: `2 |t| τ_pas = 2`. -/
theorem stepTime_two (T : TightBindingChain) (ht : T.t ≠ 0) (hN : T.N = 2) :
    2 * |T.t| * stepTime T = 2 := by
  have hta : 0 < |T.t| := abs_pos.mpr ht
  rw [stepTime_eq, hN, show ((2 : ℕ) : ℝ) + 1 = 3 by norm_num, Real.cos_pi_div_three]
  field_simp

end ProperTimeGR
