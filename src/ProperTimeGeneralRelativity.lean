/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime
public import ProperTimeGeneralRelativity.Niven
public import ProperTimeGeneralRelativity.Mass
public import ProperTimeGeneralRelativity.Equivalence
public import ProperTimeGeneralRelativity.Cube
public import ProperTimeGeneralRelativity.Gravity.EinsteinEquation

/-!
# Time counts steps, and the Einstein equation

1. **Time counts steps** (`StepTime`, on Physlib #2096). On the open tight binding chain the
   spacing `a` enters only through the position, so one step, one spacing at the speed limit,
   lasts `1 / (2 |t| cos (π / (N + 1)))` whatever `a` is. `n` steps take `n` step times, no state
   is faster, and no step means no time. The maximal current state is light at `N = 2, 3` and
   massive from `N = 4` on, with uncertainty ratio `1 < C < √(π²/3 − 2)`.
2. **The open cube NRS³** (`Cube`). On the product of three chains `Tx`, `Ty`, `Tz`, two distinct
   observables among `H_k`, `X_k` commute iff they lie on different axes; from `4 × 4 × 4` on
   the volumetric quantum `𝒱 = δ(Nx) δ(Ny) δ(Nz)` is positive and Robertson 1934 is strict in
   the maximal current state, `|det Ω| < det Σ`; and the Mandelstam–Tamm ratio of that state is
   `1 / C²` on each axis.
3. **The accelerated clock** (`Gravity.Unruh`). The Rindler worldline of acceleration `a` is
   parametrized by its proper time, its acceleration is `a`, its shortest imaginary period is
   `2π / a`, and the Unruh temperature `a / 2π` is the inverse of that period.
4. **The Einstein equation** (`Gravity.EinsteinEquation`). If the Clausius relation with the
   entropy per unit area `η = 1 / (4 ℓ²)` holds on every light sheet through every point, and
   `∇ f = ½ ∇ R` (the contracted Bianchi identity with the conservation of `T`), then
   `Ric − ½ R g + Λ g = 8π ℓ² T` for a constant `Λ`.

## Main results

- `ProperTimeGR.timeCountsSteps` : the spacing cancels and time counts steps.
- `ProperTimeGR.openCubeNRS3` : the open cube, volumetric quantum, strict Robertson 1934 and the
  Mandelstam–Tamm ratio `1 / C²` on each axis.
- `ProperTimeGR.acceleratedClock` : proper time, acceleration `a`, period `2π / a`, `T = a / 2π`.
- `ProperTimeGR.einstein_eightPi` : the Einstein equation with coupling `8π ℓ²`.
- `ProperTimeGR.properTime_generalRelativity` : items 1, 3 and 4 together.
- `ProperTimeGR.massAndEquivalence` : Niven on the step, the effective mass with `a` cancelled
  in `m* c²`, `α_G > 0`, and the weak field of a mass agreeing to first order with the
  accelerated frame (`Niven`, `Mass`, `Equivalence`).
- `ProperTimeGR.fork_unification` : the step time, the rest energy, the open cube, the
  equivalence of `g₀₀`, the Unruh temperature and the Einstein equation in one statement.
-/

@[expose] public noncomputable section

open Real
open Lorentz Vector
open LinearMap (BilinForm)
open CondensedMatter
open CondensedMatter.TightBindingChain
open scoped _root_.selfAdjoint

namespace ProperTimeGR

/-- **The accelerated clock.** The Rindler worldline of acceleration `a > 0` is parametrized by
proper time, has acceleration `a`, has shortest imaginary period `2π / a`, and the Unruh
temperature is the inverse of that period. -/
theorem acceleratedClock {a : ℝ} (ha : 0 < a) :
    (∀ τ, deriv (Rindler.time a) τ ^ 2 - deriv (Rindler.space a) τ ^ 2 = 1) ∧
    (∀ τ, deriv (deriv (Rindler.space a)) τ ^ 2 - deriv (deriv (Rindler.time a)) τ ^ 2 =
      a ^ 2) ∧
    Rindler.PeriodicInImaginaryTime a (2 * π / a) ∧
    (∀ β, 0 < β → Rindler.PeriodicInImaginaryTime a β → 2 * π / a ≤ β) ∧
    Rindler.unruhTemperature a * (2 * π / a) = 1 :=
  ⟨Rindler.velocity_norm ha.ne', Rindler.acceleration_norm ha.ne', Rindler.periodic_two_pi ha.ne',
    fun _ hβ h => Rindler.period_ge ha hβ h, Rindler.unruhTemperature_mul_period ha.ne'⟩

/-- **The Einstein equation with coupling `8π ℓ²`.** With `η = 1 / (4 ℓ²)`, the Clausius relation
on every light sheet through every point and `∇ f = ½ ∇ R` give a constant `Λ` with
`Ric − ½ R g + Λ g = 8π ℓ² T`. -/
theorem einstein_eightPi {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ric T : E → BilinForm ℝ (Vector d)} (hRic : ∀ x, (Ric x).IsSymm) (hT : ∀ x, (T x).IsSymm)
    {ℓ κs A l₀ : ℝ} (hℓ : ℓ ≠ 0) (hκ : κs ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0)
    (hC : ∀ x, ∀ k : Vector d, ⟪k, k⟫ₘ = 0 →
      LightSheet.Clausius (1 / (4 * ℓ ^ 2)) κs (Ric x k k) (T x k k) A l₀)
    (hf : Differentiable ℝ fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x))
    (hR : Differentiable ℝ fun x => trace (Ric x))
    (hBianchi : ∀ x, fderiv ℝ (fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun x => trace (Ric x)) x) :
    ∃ Λ : ℝ, ∀ x, ∀ p q, Ric x p q - trace (Ric x) / 2 * ⟪p, q⟫ₘ + Λ * ⟪p, q⟫ₘ =
      8 * π * ℓ ^ 2 * T x p q := by
  have key : 2 * π / (1 / (4 * ℓ ^ 2)) = 8 * π * ℓ ^ 2 := by
    rw [one_div, div_inv_eq_mul]
    ring
  have hη : (1 / (4 * ℓ ^ 2) : ℝ) ≠ 0 := by positivity
  obtain ⟨Λ, h⟩ := Einstein.einstein_equation hRic hT hκ hA hl hη hC (by rwa [key]) hR
    (by rwa [key])
  exact ⟨Λ, fun x p q => by rw [← key]; exact (h x).1 p q⟩

/-- **Time counts steps, and general relativity.** On a chain `C` with `t ≠ 0` and `N ≥ 2` one
step lasts `1 / (2 |t| cos (π / (N + 1)))` whatever the spacing, and `n` steps take no time iff
`n = 0`; the accelerated clock has temperature `a / 2π`; and the Clausius relation on every light
sheet gives the Einstein equation with coupling `8π ℓ²`. -/
theorem properTime_generalRelativity (C : TightBindingChain) (htC : C.t ≠ 0) (hNC : 2 ≤ C.N)
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ric T : E → BilinForm ℝ (Vector d)} (hRic : ∀ x, (Ric x).IsSymm)
    (hT : ∀ x, (T x).IsSymm) {ℓ κs A l₀ : ℝ} (hℓ : ℓ ≠ 0) (hκ : κs ≠ 0) (hA : A ≠ 0)
    (hl : l₀ ≠ 0)
    (hC : ∀ x, ∀ k : Vector d, ⟪k, k⟫ₘ = 0 →
      LightSheet.Clausius (1 / (4 * ℓ ^ 2)) κs (Ric x k k) (T x k k) A l₀)
    (hf : Differentiable ℝ fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x))
    (hR : Differentiable ℝ fun x => trace (Ric x))
    (hBianchi : ∀ x, fderiv ℝ (fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun x => trace (Ric x)) x)
    {a : ℝ} (ha : 0 < a) :
    (stepTime C = 1 / (2 * |C.t| * Real.cos (π / (C.N + 1))) ∧
      ∀ n : ℕ, elapsed C n = 0 ↔ n = 0) ∧
    Rindler.unruhTemperature a * (2 * π / a) = 1 ∧
    ∃ Λ : ℝ, ∀ x, ∀ p q, Ric x p q - trace (Ric x) / 2 * ⟪p, q⟫ₘ + Λ * ⟪p, q⟫ₘ =
      8 * π * ℓ ^ 2 * T x p q :=
  ⟨⟨stepTime_eq C, elapsed_eq_zero_iff C htC hNC⟩,
    (acceleratedClock ha).2.2.2.2,
    einstein_eightPi hRic hT hℓ hκ hA hl hC hf hR hBianchi⟩

/-- **Mass and equivalence.** From `N = 3` on the step is irrational in units of `1 / |t|`
(Niven); the effective mass of the band has rest energy `m* c² = 2 t cos² (π / (N + 1))`, without
the spacing; `α_G = G m*² / c > 0`; and at `r₀ ≠ 0` the weak field of a mass `M` has the slope of
`g₀₀` of the frame accelerated with `G M / r₀²`. -/
theorem massAndEquivalence (C : TightBindingChain) (htC : 0 < C.t) (hNC : 3 ≤ C.N)
    {G M r₀ : ℝ} (hG : 0 < G) (hr : r₀ ≠ 0) :
    (¬ ∃ q : ℚ, 2 * |C.t| * stepTime C = q) ∧
    effMass C * C.maxCurrent ^ 2 = 2 * C.t * Real.cos (π / (C.N + 1)) ^ 2 ∧
    0 < gravitationalCoupling C G ∧
    (HasDerivAt (fun r => -(1 + 2 * Frame.newtonPotential G M r)) (-2 * (G * M / r₀ ^ 2)) r₀ ∧
      HasDerivAt (Frame.g00 (G * M / r₀ ^ 2)) (-2 * (G * M / r₀ ^ 2)) 0) :=
  ⟨stepTime_irrational C htC.ne' hNC, effMass_mul_maxCurrent_sq C htC,
    gravitationalCoupling_pos C hG htC (by omega), Frame.equivalence G M hr⟩

/-- **The open cube NRS³.** On the product of three chains with `t ≠ 0` and `N ≥ 4`: two
distinct observables among `H_k`, `X_k` commute iff they lie on different axes; the volumetric
quantum `𝒱 = δ(Nx) δ(Ny) δ(Nz)` is positive; Robertson 1934 is strict in the maximal current
state; and the Mandelstam–Tamm ratio of that state is `1 / C²` on each axis. -/
theorem openCubeNRS3 (Tx Ty Tz : TightBindingChain)
    (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    (∀ p q : Fin 2 × Fin 3, p ≠ q →
      (⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 ↔ p.2 ≠ q.2)) ∧
    0 < Tx.volQuantum Ty Tz ∧
    |((Tx.maxCurrentCubeVectorState Ty Tz).bracketMatrix (Tx.cubePairs Ty Tz)).det| <
      ((Tx.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (Tx.cubePairs Ty Tz)).det ∧
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
  ⟨fun _ _ h => Cube.pairs_commute_iff Tx Ty Tz hx hy hz (by omega) (by omega) (by omega) h,
   Cube.volQuantum_pos Tx Ty Tz hx hy hz hNx hNy hNz,
   Cube.robertson_det_strict Tx Ty Tz hx hy hz hNx hNy hNz,
   Cube.mandelstamTamm_efficiency Tx Ty Tz⟩

/-- **The steps together.** One statement on the chain `C` and the cube `C × Ty × Tz`:
1. **Step time** (on Physlib's `TightBindingChain`, Joseph Tooby-Smith, and #2096): the spacing
   cancels in `τ_pas = 1 / (2 |t| cos (π / (N + 1)))` and in `m* c² = 2 t cos² (π / (N + 1))`.
2. **Open cube** (Physlib #1756, #1742): `𝒱 > 0` and, in the maximal current state, Robertson
   1934 strict from `4 × 4 × 4` on.
3. **Equivalence** (`Equivalence`): the weak field of `M` has the slope of `g₀₀` of the frame
   accelerated with `G M / r₀²`.
4. **Einstein** (`Gravity`): the Unruh temperature `a / 2π` and, from the Clausius relation on
   every light sheet, `Ric − ½ R g + Λ g = 8π ℓ² T`. -/
theorem fork_unification (C : TightBindingChain) (htC : 0 < C.t) (hNC : 4 ≤ C.N)
    (Ty Tz : TightBindingChain) (hy : 0 < Ty.t) (hz : 0 < Tz.t) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    {G M r₀ : ℝ} (hr : r₀ ≠ 0)
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ric T : E → BilinForm ℝ (Vector d)} (hRic : ∀ x, (Ric x).IsSymm) (hT : ∀ x, (T x).IsSymm)
    {ℓ κs A l₀ : ℝ} (hℓ : ℓ ≠ 0) (hκ : κs ≠ 0) (hA : A ≠ 0) (hl : l₀ ≠ 0)
    (hC : ∀ x, ∀ k : Vector d, ⟪k, k⟫ₘ = 0 →
      LightSheet.Clausius (1 / (4 * ℓ ^ 2)) κs (Ric x k k) (T x k k) A l₀)
    (hf : Differentiable ℝ fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x))
    (hR : Differentiable ℝ fun x => trace (Ric x))
    (hBianchi : ∀ x, fderiv ℝ (fun x => Einstein.fScalar (8 * π * ℓ ^ 2) (Ric x) (T x)) x =
      (1 / 2 : ℝ) • fderiv ℝ (fun x => trace (Ric x)) x)
    {a : ℝ} (ha : 0 < a) :
    stepTime C = 1 / (2 * |C.t| * Real.cos (π / (C.N + 1))) ∧
    effMass C * C.maxCurrent ^ 2 = 2 * C.t * Real.cos (π / (C.N + 1)) ^ 2 ∧
    0 < C.volQuantum Ty Tz ∧
    |((C.maxCurrentCubeVectorState Ty Tz).bracketMatrix (C.cubePairs Ty Tz)).det| <
      ((C.maxCurrentCubeVectorState Ty Tz).covarianceMatrix (C.cubePairs Ty Tz)).det ∧
    (HasDerivAt (fun r => -(1 + 2 * Frame.newtonPotential G M r)) (-2 * (G * M / r₀ ^ 2)) r₀ ∧
      HasDerivAt (Frame.g00 (G * M / r₀ ^ 2)) (-2 * (G * M / r₀ ^ 2)) 0) ∧
    Rindler.unruhTemperature a * (2 * π / a) = 1 ∧
    ∃ Λ : ℝ, ∀ x, ∀ p q, Ric x p q - trace (Ric x) / 2 * ⟪p, q⟫ₘ + Λ * ⟪p, q⟫ₘ =
      8 * π * ℓ ^ 2 * T x p q :=
  ⟨stepTime_eq C,
   effMass_mul_maxCurrent_sq C htC,
   Cube.volQuantum_pos C Ty Tz htC.ne' hy.ne' hz.ne' hNC hNy hNz,
   Cube.robertson_det_strict C Ty Tz htC.ne' hy.ne' hz.ne' hNC hNy hNz,
   Frame.equivalence G M hr,
   (acceleratedClock ha).2.2.2.2,
   einstein_eightPi hRic hT hℓ hκ hA hl hC hf hR hBianchi⟩

end ProperTimeGR
