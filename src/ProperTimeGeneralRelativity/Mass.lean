/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime

/-!
# The effective mass of the band, and a rest energy without the spacing

The band of the chain is `E(k) = E₀ − 2 t cos (k a)`, the formula of Physlib's
`TightBindingChain.energyEigenvalue`. Its curvature at `k = 0` is `E''(0) = 2 t a²`, and the
effective mass is `m* = 1 / E''(0)` (`ħ = 1`). With the speed limit `c = maxCurrent` as the speed
of the chain, the spacing cancels again in the rest energy: `m* c² = 2 t cos² (π / (N + 1))`, and
`m* c² τ_pas = cos (π / (N + 1))`. The mass `m*` itself keeps `a`, and so does the
gravitational coupling `α_G = G m*² / c`, which is positive.

## Main results

- `ProperTimeGR.deriv_deriv_band_zero` : `E''(0) = 2 t a²`.
- `ProperTimeGR.effMass_eq` : `m* = 1 / (2 t a²)`.
- `ProperTimeGR.effMass_mul_maxCurrent_sq` : `m* c² = 2 t cos² (π / (N + 1))`, without `a`.
- `ProperTimeGR.restEnergy_mul_stepTime` : `m* c² τ_pas = cos (π / (N + 1))`.
- `ProperTimeGR.gravitationalCoupling_pos` : `α_G = G m*² / c > 0`.
-/

@[expose] public noncomputable section

open Real CondensedMatter

namespace ProperTimeGR

variable (T : TightBindingChain)

/-- The band `E(k) = E₀ − 2 t cos (k a)` for every real `k`. -/
def band (k : ℝ) : ℝ := T.E0 - 2 * T.t * Real.cos (k * T.a)

/-- On the quantized wavenumbers the band is Physlib's energy eigenvalue. -/
theorem band_eq_energyEigenvalue (k : T.QuantaWaveNumber) : band T k = T.energyEigenvalue k :=
  rfl

theorem hasDerivAt_band (k : ℝ) :
    HasDerivAt (band T) (2 * T.t * T.a * Real.sin (k * T.a)) k := by
  have h1 : HasDerivAt (fun k : ℝ => k * T.a) T.a k := by
    simpa using (hasDerivAt_id k).mul_const T.a
  have h3 := (((Real.hasDerivAt_cos (k * T.a)).comp k h1).const_mul (2 * T.t)).const_sub T.E0
  exact h3.congr_deriv (by ring)

theorem deriv_band : deriv (band T) = fun k => 2 * T.t * T.a * Real.sin (k * T.a) :=
  funext fun k => (hasDerivAt_band T k).deriv

theorem hasDerivAt_deriv_band (k : ℝ) :
    HasDerivAt (deriv (band T)) (2 * T.t * T.a ^ 2 * Real.cos (k * T.a)) k := by
  rw [deriv_band]
  have h1 : HasDerivAt (fun k : ℝ => k * T.a) T.a k := by
    simpa using (hasDerivAt_id k).mul_const T.a
  have h2 := ((Real.hasDerivAt_sin (k * T.a)).comp k h1).const_mul (2 * T.t * T.a)
  exact h2.congr_deriv (by ring)

/-- **The curvature of the band.** `E''(0) = 2 t a²`. -/
theorem deriv_deriv_band_zero : deriv (deriv (band T)) 0 = 2 * T.t * T.a ^ 2 := by
  rw [(hasDerivAt_deriv_band T 0).deriv]
  simp

/-- The effective mass `m* = 1 / E''(0)`, with `ħ = 1`. -/
def effMass : ℝ := 1 / deriv (deriv (band T)) 0

theorem effMass_eq : effMass T = 1 / (2 * T.t * T.a ^ 2) := by
  rw [effMass, deriv_deriv_band_zero]

theorem effMass_pos (ht : 0 < T.t) : 0 < effMass T := by
  rw [effMass_eq]
  have := T.a_pos
  positivity

/-- **The spacing cancels in the rest energy.** `m* c² = 2 t cos² (π / (N + 1))`. -/
theorem effMass_mul_maxCurrent_sq (ht : 0 < T.t) :
    effMass T * T.maxCurrent ^ 2 = 2 * T.t * Real.cos (π / (T.N + 1)) ^ 2 := by
  have ha := T.a_pos
  rw [effMass_eq, TightBindingChain.maxCurrent, abs_mul, abs_of_pos ha, abs_of_pos ht]
  field_simp

/-- **Rest energy times the step.** `m* c² τ_pas = cos (π / (N + 1))`. -/
theorem restEnergy_mul_stepTime (ht : 0 < T.t) (hN : 2 ≤ T.N) :
    effMass T * T.maxCurrent ^ 2 * stepTime T = Real.cos (π / (T.N + 1)) := by
  have hc : 0 < Real.cos (π / (T.N + 1)) := cos_pi_div_succ_pos hN
  rw [effMass_mul_maxCurrent_sq T ht, stepTime_eq, abs_of_pos ht]
  field_simp

/-- The gravitational coupling `α_G = G m*² / c` with `c = maxCurrent` (`ħ = 1`). -/
def gravitationalCoupling (G : ℝ) : ℝ := G * effMass T ^ 2 / T.maxCurrent

theorem gravitationalCoupling_pos {G : ℝ} (hG : 0 < G) (ht : 0 < T.t) (hN : 2 ≤ T.N) :
    0 < gravitationalCoupling T G := by
  have hm := effMass_pos T ht
  have hc : 0 < Real.cos (π / (T.N + 1)) := cos_pi_div_succ_pos hN
  have hv : 0 < T.maxCurrent := by
    unfold TightBindingChain.maxCurrent
    have := abs_pos.mpr (mul_ne_zero T.a_pos.ne' ht.ne')
    positivity
  unfold gravitationalCoupling
  positivity

end ProperTimeGR
