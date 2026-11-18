/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.VolumetricQuantum
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.MandelstamTamm

/-!
# The open tight binding cube: three commuting axes and Robertson 1934

On the Cartesian product of three open tight binding chains `Tx`, `Ty`, `Tz`, the three axes
commute: `[alongX, alongY] = 0`, `[alongX, alongZ] = 0`, `[alongY, alongZ] = 0`.
The six observables `(H, X)` satisfy Robertson's determinant relation `|det Ω| ≤ det Σ`.
In the maximal current state, `det Σ = (C_x C_y C_z)² |det Ω|`.
For `Nx, Ny, Nz ≥ 4`, Robertson 1934 is strict: `|det Ω| < det Σ`.
The volumetric quantum `𝒱 = δ(Nx) δ(Ny) δ(Nz)` is strictly positive for `Nx, Ny, Nz ≥ 4`, and
vanishes if any axis has `N ∈ {2, 3}` (Physlib `volQuantum_eq_zero_iff`).
On each axis, the Mandelstam–Tamm ratio is `1 / C²`.

## Main results

- `ProperTimeGR.Cube.axes_commute` : observables of distinct axes commute.
- `ProperTimeGR.Cube.robertson_det` : Robertson 1934 for the six observables on the cube.
- `ProperTimeGR.Cube.det_cov_maxCurrentCubeState` : `det Σ = (C_x C_y C_z)² |det Ω|`.
- `ProperTimeGR.Cube.robertson_det_strict` : strict from `4 × 4 × 4`.
- `ProperTimeGR.Cube.volQuantum_pos` : volumetric quantum is positive from `4 × 4 × 4`.
- `ProperTimeGR.Cube.mandelstamTamm_efficiency` : Mandelstam–Tamm ratio along `X` is `1 / C_x²`.
-/

@[expose] public noncomputable section

open scoped ComplexOrder _root_.selfAdjoint QuantumMechanics.FiniteHilbertSpace
open PhyslibAlpha.ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap
open CondensedMatter
open CondensedMatter.TightBindingChain

namespace ProperTimeGR.Cube

variable (Tx Ty Tz : TightBindingChain)

/-- **Distinct axes commute.** Observables acting on different axes of the cube commute. -/
theorem axes_commute (Ax : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace))
    (Ay : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace))
    (Az : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    ⁅Tx.alongX Ty Tz Ax, Tx.alongY Ty Tz Ay⁆ = 0 ∧
    ⁅Tx.alongX Ty Tz Ax, Tx.alongZ Ty Tz Az⁆ = 0 ∧
    ⁅Tx.alongY Ty Tz Ay, Tx.alongZ Ty Tz Az⁆ = 0 :=
  ⟨Tx.bracket_alongX_alongY Ty Tz Ax Ay,
   Tx.bracket_alongX_alongZ Ty Tz Ax Az,
   Tx.bracket_alongY_alongZ Ty Tz Ay Az⟩

/-- **Robertson 1934 on the six observables of the cube.** -/
theorem robertson_det (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) :
    (Tx.axisBracket Ty Tz ω 0 * Tx.axisBracket Ty Tz ω 1 * Tx.axisBracket Ty Tz ω 2) ^ 2 ≤
      (covarianceMatrix ω (Tx.cubePairs Ty Tz)).det :=
  robertson_det_cube Tx Ty Tz ω

/-- **Determinant ratio in the maximal current state.**
`det Σ = (C_x C_y C_z)² |det Ω|`. -/
theorem det_cov_maxCurrentCubeState (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    ((Tx.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (Tx.cubePairs Ty Tz)).det =
      (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2 *
        (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
              Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
            Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 :=
  det_covarianceMatrix_maxCurrentCubeState Tx Ty Tz hx hy hz hNx hNy hNz

/-- **Robertson 1934 is strict on the cube from 4 × 4 × 4.** -/
theorem robertson_det_strict (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    |((Tx.maxCurrentCubeVectorState Ty Tz).bracketMatrix (Tx.cubePairs Ty Tz)).det| <
      ((Tx.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (Tx.cubePairs Ty Tz)).det :=
  robertson_det_maxCurrentCubeState_strict Tx Ty Tz hx hy hz hNx hNy hNz

/-- **Positivity of the volumetric quantum.** From `4 × 4 × 4` on, `𝒱 = δ(Nx) δ(Ny) δ(Nz) > 0`. -/
theorem volQuantum_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    0 < Tx.volQuantum Ty Tz :=
  CondensedMatter.TightBindingChain.volQuantum_pos hx hy hz hNx hNy hNz

/-- **Mandelstam–Tamm efficiency on the cube.** Along `x`, the efficiency is `1 / C_x²`. -/
theorem mandelstamTamm_efficiency :
    (Tx.maxCurrentCubeVectorState Ty Tz).expectation (Tx.alongX Ty Tz Tx.currentObservable) ^ 2 /
        (4 * ((Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongX Ty Tz Tx.openHamiltonianObservable) *
            (Tx.maxCurrentCubeVectorState Ty Tz).variance
              (Tx.alongX Ty Tz Tx.positionObservable))) =
      1 / Tx.uncertaintyRatio ^ 2 :=
  mandelstamTammRatio_alongX Tx Ty Tz

end ProperTimeGR.Cube
