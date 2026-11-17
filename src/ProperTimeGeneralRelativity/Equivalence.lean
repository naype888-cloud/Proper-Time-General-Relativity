/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.Gravity.Unruh
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# The accelerated frame, `g₀₀`, and the equivalence principle

In units `c = 1`, the frame of acceleration `α` is `t = (1/α + ξ) sinh (α η)`,
`x = (1/α + ξ) cosh (α η)`. At `ξ = 0` it is the Rindler worldline of `Gravity.Unruh`. The
Minkowski interval in these coordinates is `−(1 + α ξ)² dη² + dξ²`, so
`g₀₀ = −(1 + α ξ)² = −(1 + 2Φ) − Φ²` with `Φ = α ξ`: to first order it is the weak field
`g₀₀ = −(1 + 2Φ/c²)`, and a static clock at height `ξ` runs at `1 + α ξ`.

The Newtonian potential `Φ(r) = −G M / r` has slope `G M / r₀²` at `r₀`. So the weak field
`−(1 + 2Φ)` at `r₀` and the accelerated frame with `α = G M / r₀²` at `ξ = 0` have the same slope
of `g₀₀`: to first order, the field of the mass is the accelerated frame. Their values differ by
the constant `2 G M / r₀`, the choice of the clock at `ξ = 0`.

## Main results

- `ProperTimeGR.Frame.metric` : `g_ηη = −(1 + α ξ)²`, `g_ξξ = 1`, `g_ηξ = 0`.
- `ProperTimeGR.Frame.time_zero`, `ProperTimeGR.Frame.space_zero` : at `ξ = 0`, the Rindler
  worldline.
- `ProperTimeGR.Frame.g00_eq_weakField` : `g₀₀ = −(1 + 2Φ) − Φ²`.
- `ProperTimeGR.Frame.clockRate` : `√(−g₀₀) = 1 + α ξ`.
- `ProperTimeGR.Frame.equivalence` : the weak field of `M` and the frame of acceleration
  `G M / r₀²` agree to first order.
-/

@[expose] public noncomputable section

open Real

namespace ProperTimeGR.Frame

variable (α : ℝ)

/-- The time coordinate of the accelerated frame. -/
def time (η ξ : ℝ) : ℝ := (1 / α + ξ) * Real.sinh (α * η)

/-- The space coordinate of the accelerated frame. -/
def space (η ξ : ℝ) : ℝ := (1 / α + ξ) * Real.cosh (α * η)

theorem time_zero (η : ℝ) : time α η 0 = Rindler.time α η := by
  simp [time, Rindler.time, div_eq_inv_mul]

theorem space_zero (η : ℝ) : space α η 0 = Rindler.space α η := by
  simp [space, Rindler.space, div_eq_inv_mul]

theorem hasDerivAt_time_eta (hα : α ≠ 0) (η ξ : ℝ) :
    HasDerivAt (fun η => time α η ξ) ((1 + α * ξ) * Real.cosh (α * η)) η := by
  have h := ((Real.hasDerivAt_sinh (α * η)).comp η
    ((hasDerivAt_id η).const_mul α)).const_mul (1 / α + ξ)
  exact h.congr_deriv (by field_simp)

theorem hasDerivAt_space_eta (hα : α ≠ 0) (η ξ : ℝ) :
    HasDerivAt (fun η => space α η ξ) ((1 + α * ξ) * Real.sinh (α * η)) η := by
  have h := ((Real.hasDerivAt_cosh (α * η)).comp η
    ((hasDerivAt_id η).const_mul α)).const_mul (1 / α + ξ)
  exact h.congr_deriv (by field_simp)

theorem hasDerivAt_time_xi (η ξ : ℝ) :
    HasDerivAt (fun ξ => time α η ξ) (Real.sinh (α * η)) ξ := by
  exact (((hasDerivAt_id ξ).const_add (1 / α)).mul_const (Real.sinh (α * η))).congr_deriv
    (one_mul _)

theorem hasDerivAt_space_xi (η ξ : ℝ) :
    HasDerivAt (fun ξ => space α η ξ) (Real.cosh (α * η)) ξ := by
  exact (((hasDerivAt_id ξ).const_add (1 / α)).mul_const (Real.cosh (α * η))).congr_deriv
    (one_mul _)

/-- **The metric of the accelerated frame.** `−dt² + dx² = −(1 + α ξ)² dη² + dξ²`. -/
theorem metric (hα : α ≠ 0) (η ξ : ℝ) :
    -(deriv (fun η => time α η ξ) η) ^ 2 + (deriv (fun η => space α η ξ) η) ^ 2 =
      -(1 + α * ξ) ^ 2 ∧
    -(deriv (fun ξ => time α η ξ) ξ) ^ 2 + (deriv (fun ξ => space α η ξ) ξ) ^ 2 = 1 ∧
    -(deriv (fun η => time α η ξ) η) * (deriv (fun ξ => time α η ξ) ξ) +
      (deriv (fun η => space α η ξ) η) * (deriv (fun ξ => space α η ξ) ξ) = 0 := by
  rw [(hasDerivAt_time_eta α hα η ξ).deriv, (hasDerivAt_space_eta α hα η ξ).deriv,
    (hasDerivAt_time_xi α η ξ).deriv, (hasDerivAt_space_xi α η ξ).deriv]
  have h := Real.cosh_sq (α * η)
  refine ⟨by linear_combination (-(1 + α * ξ) ^ 2) * h, by linear_combination h, by ring⟩

/-- The time component of the metric of the accelerated frame. -/
def g00 (ξ : ℝ) : ℝ := -(1 + α * ξ) ^ 2

/-- **The weak field.** `g₀₀ = −(1 + 2Φ) − Φ²` with `Φ = α ξ`. -/
theorem g00_eq_weakField (ξ : ℝ) : g00 α ξ = -(1 + 2 * (α * ξ)) - (α * ξ) ^ 2 := by
  unfold g00
  ring

/-- **A static clock at height `ξ` runs at `1 + α ξ`.** -/
theorem clockRate {ξ : ℝ} (hξ : 0 ≤ 1 + α * ξ) : √(-g00 α ξ) = 1 + α * ξ := by
  unfold g00
  rw [neg_neg, Real.sqrt_sq hξ]

theorem hasDerivAt_g00 (ξ : ℝ) : HasDerivAt (g00 α) (-(2 * (1 + α * ξ) * α)) ξ := by
  have h0 : HasDerivAt (fun y => 1 + α * id y) (α * 1) ξ :=
    ((hasDerivAt_id ξ).const_mul α).const_add 1
  have h := (h0.pow 2).neg
  exact h.congr_deriv (by simp)

/-- The Newtonian potential of a mass `M`. -/
def newtonPotential (G M r : ℝ) : ℝ := -(G * M) / r

theorem hasDerivAt_newtonPotential (G M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (newtonPotential G M) (G * M / r ^ 2) r := by
  have h := (hasDerivAt_inv hr).const_mul (-(G * M))
  convert h using 1
  · funext x
    simp [newtonPotential, div_eq_mul_inv]
  · field_simp

/-- **Equivalence.** At `r₀`, the weak field `−(1 + 2Φ)` of a mass `M` and the accelerated frame
with `α = G M / r₀²` (at `ξ = 0`) have the same slope of `g₀₀`. -/
theorem equivalence (G M : ℝ) {r₀ : ℝ} (hr : r₀ ≠ 0) :
    HasDerivAt (fun r => -(1 + 2 * newtonPotential G M r)) (-2 * (G * M / r₀ ^ 2)) r₀ ∧
    HasDerivAt (g00 (G * M / r₀ ^ 2)) (-2 * (G * M / r₀ ^ 2)) 0 := by
  refine ⟨?_, ?_⟩
  · have h := ((hasDerivAt_newtonPotential G M hr).const_mul 2).const_add 1 |>.neg
    convert h using 1
    ring
  · convert hasDerivAt_g00 (G * M / r₀ ^ 2) 0 using 1
    ring

end ProperTimeGR.Frame
