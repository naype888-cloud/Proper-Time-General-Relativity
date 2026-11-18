/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.Equivalence
public import PhyslibAlpha.ClassicalMechanics.OrbitalMechanics.NewtonianGravity
public import PhyslibAlpha.Relativity.General.Schwarzschild.IncompressibleSphere

/-!
# Bridges to Newtonian gravity and to the exterior Schwarzschild metric in Physlib

The equivalence of `Equivalence` compares the weak field `−(1 + 2Φ)`, `Φ = −G M / r`, with the
frame of acceleration `G M / r₀²`. Two files of Physlib give these two objects.

1. **Newtonian gravity by pairs** (Qianli Ma,
   `PhyslibAlpha/ClassicalMechanics/OrbitalMechanics/NewtonianGravity.lean`). The acceleration
   of a target due to a source of mass `m` at displacement `d ≠ 0` is
   `pairGravityAcceleration = (G m / ‖d‖³) • d`; its norm is `G m / ‖d‖²`. So with `M = m` and
   `r₀ = ‖d‖` it is the acceleration `G M / r₀²` of `Frame.equivalence`.
2. **The exterior Schwarzschild metric** (Philippe Kevorkian,
   `PhyslibAlpha/Relativity/General/Schwarzschild/IncompressibleSphere.lean`). Outside the
   incompressible sphere `g_tt = 1 − r_s / r`, in signature `(+, −)`. If `r_s = 2 G M`, then
   `−(1 + 2Φ(r)) = −g_tt(r)` for every `r`: the weak field of `Equivalence` is exactly the
   exterior metric, written in signature `(−, +)`, and not only its first order.

## Main results

- `ProperTimeGR.Bridges.norm_pairGravityAcceleration` : `‖a‖ = G m / ‖d‖²`.
- `ProperTimeGR.Bridges.equivalence_pairGravity` : the frame accelerated with `‖a‖` has, at
  `‖d‖`, the slope of `g₀₀` of the weak field of the source.
- `ProperTimeGR.Bridges.weakField_eq_neg_gttOut` : `−(1 + 2Φ) = −g_tt` when `r_s = 2 G M`.
- `ProperTimeGR.Bridges.equivalence_gttOut` : at `r₀ ≠ 0`, `−g_tt` has the slope of `g₀₀` of the
  frame accelerated with `r_s / (2 r₀²)`.
-/

@[expose] public noncomputable section

open ClassicalMechanics ClassicalMechanics.ReferenceFrame GeneralRelativity

namespace ProperTimeGR.Bridges

section Newton

open scoped Classical

variable {d : ℕ} {frame : ReferenceFrame d} [Fact frame.IsMetricConserved]
variable {particles : Multiset frame.Particle}

/-- **The norm of Qianli Ma's pair acceleration.** For `G ≥ 0` and a nonzero displacement `d`,
`‖pairGravityAcceleration‖ = G m / ‖d‖²`. -/
theorem norm_pairGravityAcceleration {G : ℝ} (hG : 0 ≤ G) (source target : particles) (t : ℝ)
    (h : source.1.pos t ≠ target.1.pos t) :
    ‖pairGravityAcceleration G particles source target t‖ =
      G * source.1.mass.val / ‖source.1.pos t - target.1.pos t‖ ^ 2 := by
  have hd : 0 < ‖source.1.pos t - target.1.pos t‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have hm : 0 ≤ G * source.1.mass.val := mul_nonneg hG source.1.mass.2.le
  simp only [pairGravityAcceleration]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp

/-- **Equivalence with Newtonian gravity by pairs.** At `r₀ = ‖d‖`, the weak field of the source
mass and the frame accelerated with the norm of Qianli Ma's pair acceleration have the same
slope of `g₀₀`. -/
theorem equivalence_pairGravity {G : ℝ} (hG : 0 ≤ G) (source target : particles) (t : ℝ)
    (h : source.1.pos t ≠ target.1.pos t) :
    let r₀ := ‖source.1.pos t - target.1.pos t‖
    let α := ‖pairGravityAcceleration G particles source target t‖
    HasDerivAt (fun r => -(1 + 2 * Frame.newtonPotential G source.1.mass.val r)) (-2 * α) r₀ ∧
      HasDerivAt (Frame.g00 α) (-2 * α) 0 := by
  intro r₀ α
  have hr : r₀ ≠ 0 := (norm_pos_iff.mpr (sub_ne_zero.mpr h)).ne'
  have hα : α = G * source.1.mass.val / r₀ ^ 2 :=
    norm_pairGravityAcceleration hG source target t h
  rw [hα]
  exact Frame.equivalence G source.1.mass.val hr

end Newton

section Schwarzschild

variable (S : IncompressibleSphere)

/-- **The weak field is the exterior Schwarzschild metric.** If `r_s = 2 G M`, then
`−(1 + 2Φ(r)) = −g_tt(r)` for every `r`, with Philippe Kevorkian's `g_tt = 1 − r_s / r`. -/
theorem weakField_eq_neg_gttOut {G M : ℝ} (h : S.rs = 2 * G * M) (r : ℝ) :
    -(1 + 2 * Frame.newtonPotential G M r) = -S.gttOut r := by
  simp only [Frame.newtonPotential, IncompressibleSphere.gttOut, h]
  ring

/-- **Equivalence for the exterior Schwarzschild metric.** At `r₀ ≠ 0`, `−g_tt` and the frame
accelerated with `r_s / (2 r₀²)` have the same slope of `g₀₀`. -/
theorem equivalence_gttOut {r₀ : ℝ} (hr : r₀ ≠ 0) :
    HasDerivAt (fun r => -S.gttOut r) (-2 * (S.rs / (2 * r₀ ^ 2))) r₀ ∧
      HasDerivAt (Frame.g00 (S.rs / (2 * r₀ ^ 2))) (-2 * (S.rs / (2 * r₀ ^ 2))) 0 := by
  have h := Frame.equivalence (S.rs / 2) 1 hr
  have hS : S.rs = 2 * (S.rs / 2) * 1 := by ring
  have hfun : (fun r => -(1 + 2 * Frame.newtonPotential (S.rs / 2) 1 r)) =
      fun r => -S.gttOut r := funext (weakField_eq_neg_gttOut S hS)
  have hα : S.rs / 2 * 1 / r₀ ^ 2 = S.rs / (2 * r₀ ^ 2) := by field_simp
  rw [hfun, hα] at h
  exact h

end Schwarzschild

end ProperTimeGR.Bridges
