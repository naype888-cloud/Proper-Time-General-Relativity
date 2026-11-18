/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.AxisCommutation
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.VolumetricQuantum
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.MandelstamTamm

/-!
# The open tight binding cube: three commuting axes and Robertson 1934

On the product of three open tight binding chains `Tx`, `Ty`, `Tz`, observables placed on
different axes commute (Physlib #1725). Of the six observables `H_k`, `X_k` (`k = x, y, z`), two
distinct ones commute if and only if they lie on different axes (Physlib #1986).

Robertson's relation for several observables (Physlib #1730) on the six observables reads
`(b_x b_y b_z)² ≤ det Σ` with `b_k = ω⟨⁅H_k, X_k⁆⟩`. In the maximal current state of the cube,
`det Σ = (C_x C_y C_z)² (b_x b_y b_z)²`, and from `4 × 4 × 4` on `|det Ω| < det Σ` (Physlib
#1742). The volumetric quantum `𝒱 = δ(Nx) δ(Ny) δ(Nz)` is strictly positive from `4 × 4 × 4` on
(Physlib #1756). On each axis the Mandelstam–Tamm ratio of the maximal current state of the cube
is `1 / C²` (Physlib #1739).

## Main results

- `ProperTimeGR.Cube.axes_commute` : observables of different axes commute.
- `ProperTimeGR.Cube.pairs_commute_iff` : two distinct observables among the six commute iff
  they lie on different axes.
- `ProperTimeGR.Cube.robertson_det` : `(b_x b_y b_z)² ≤ det Σ` in every state.
- `ProperTimeGR.Cube.det_cov_maxCurrentCubeState` : `det Σ = (C_x C_y C_z)² (b_x b_y b_z)²`.
- `ProperTimeGR.Cube.robertson_det_strict` : `|det Ω| < det Σ` from `4 × 4 × 4` on.
- `ProperTimeGR.Cube.volQuantum_pos` : `𝒱 > 0` from `4 × 4 × 4` on.
- `ProperTimeGR.Cube.mandelstamTamm_efficiency` : the Mandelstam–Tamm ratio is `1 / C²` on each
  axis.
-/

@[expose] public noncomputable section

open scoped ComplexOrder _root_.selfAdjoint QuantumMechanics.FiniteHilbertSpace
open PhyslibAlpha.ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap
open CondensedMatter
open CondensedMatter.TightBindingChain

namespace ProperTimeGR.Cube

variable (Tx Ty Tz : TightBindingChain)

/-- **Different axes commute** (Physlib #1725). -/
theorem axes_commute (Ax : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
    (Ay : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace))
    (Az : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    ⁅Tx.alongX Ty Tz Ax, Tx.alongY Ty Tz Ay⁆ = 0 ∧
    ⁅Tx.alongX Ty Tz Ax, Tx.alongZ Ty Tz Az⁆ = 0 ∧
    ⁅Tx.alongY Ty Tz Ay, Tx.alongZ Ty Tz Az⁆ = 0 :=
  ⟨Tx.bracket_alongX_alongY Ty Tz Ax Ay,
   Tx.bracket_alongX_alongZ Ty Tz Ax Az,
   Tx.bracket_alongY_alongZ Ty Tz Ay Az⟩

/-- **Commuting iff on different axes** (Physlib #1986). Of the six observables `H_k`, `X_k`,
two distinct ones commute if and only if they lie on different axes. -/
theorem pairs_commute_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) {p q : Fin 2 × Fin 3} (h : p ≠ q) :
    ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 ↔ p.2 ≠ q.2 :=
  bracket_cubePairs_eq_zero_iff hx hy hz hNx hNy hNz h

/-- **Robertson 1934 on the six observables of the cube** (Physlib #1730, #1742).
`(b_x b_y b_z)² ≤ det Σ` in every state, with `b_k = ω⟨⁅H_k, X_k⁆⟩`. -/
theorem robertson_det (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) :
    (Tx.axisBracket Ty Tz ω 0 * Tx.axisBracket Ty Tz ω 1 * Tx.axisBracket Ty Tz ω 2) ^ 2 ≤
      (covarianceMatrix ω (Tx.cubePairs Ty Tz)).det :=
  robertson_det_cube Tx Ty Tz ω

/-- **The covariance determinant of the maximal current state** (Physlib #1742).
`det Σ = (C_x C_y C_z)² (b_x b_y b_z)²`. -/
theorem det_cov_maxCurrentCubeState (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    ((Tx.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (Tx.cubePairs Ty Tz)).det =
      (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2 *
        (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
              Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
            Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 :=
  det_covarianceMatrix_maxCurrentCubeState Tx Ty Tz hx hy hz hNx hNy hNz

/-- **Robertson 1934 is strict in the maximal current state from `4 × 4 × 4` on**
(Physlib #1742). -/
theorem robertson_det_strict (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    |((Tx.maxCurrentCubeVectorState Ty Tz).bracketMatrix (Tx.cubePairs Ty Tz)).det| <
      ((Tx.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (Tx.cubePairs Ty Tz)).det :=
  robertson_det_maxCurrentCubeState_strict Tx Ty Tz hx hy hz hNx hNy hNz

/-- **The volumetric quantum is positive from `4 × 4 × 4` on** (Physlib #1756).
`𝒱 = δ(Nx) δ(Ny) δ(Nz) > 0`. -/
theorem volQuantum_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    0 < Tx.volQuantum Ty Tz :=
  CondensedMatter.TightBindingChain.volQuantum_pos hx hy hz hNx hNy hNz

/-- **Mandelstam–Tamm on each axis** (Physlib #1739). In the maximal current state of the cube,
`⟨J_k⟩² / (4 Var H_k Var X_k) = 1 / C_k²` for `k = x, y, z`. -/
theorem mandelstamTamm_efficiency :
    (Tx.maxCurrentCubeVectorState Ty Tz).expectation (Tx.alongX Ty Tz Tx.currentObservable) ^ 2 /
        (4 * ((Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongX Ty Tz Tx.openHamiltonianObservable) *
            (Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongX Ty Tz Tx.positionObservable))) =
      1 / Tx.uncertaintyRatio ^ 2 ∧
    (Tx.maxCurrentCubeVectorState Ty Tz).expectation (Tx.alongY Ty Tz Ty.currentObservable) ^ 2 /
        (4 * ((Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongY Ty Tz Ty.openHamiltonianObservable) *
            (Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongY Ty Tz Ty.positionObservable))) =
      1 / Ty.uncertaintyRatio ^ 2 ∧
    (Tx.maxCurrentCubeVectorState Ty Tz).expectation (Tx.alongZ Ty Tz Tz.currentObservable) ^ 2 /
        (4 * ((Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) *
            (Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongZ Ty Tz Tz.positionObservable))) =
      1 / Tz.uncertaintyRatio ^ 2 :=
  ⟨mandelstamTammRatio_alongX Tx Ty Tz, mandelstamTammRatio_alongY Tx Ty Tz,
    mandelstamTammRatio_alongZ Tx Ty Tz⟩

end ProperTimeGR.Cube
