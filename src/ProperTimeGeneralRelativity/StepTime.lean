/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Current.SpeedLimit
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.Saturation
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.LongChainMonotonicity
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Open.Basic

/-!
# Time counts steps: the spacing cancels

On the open tight binding chain the position is `X = ∑ n, a n |n⟩⟨n|` and the Hamiltonian is
`E₀ I − t A(P_N)`, the hopping of the path graph (Physlib #2096). The spacing `a` enters only
through `X`, so the current `J = i [H, X]` carries one factor `a`, and no state moves faster than
`maxCurrent = 2 |a t| cos (π / (N + 1))` (`abs_expectation_current_le`).

One step is one spacing at the speed limit. Its duration `a / maxCurrent` does not depend on `a`:
the spacing cancels and time counts steps. `n` steps take `n` step times, no state crosses `n`
spacings faster, the maximal current state crosses them exactly that fast, and no step means no
time.

## Main results

- `ProperTimeGR.stepTime_eq` : `a / maxCurrent = 1 / (2 |t| cos (π / (N + 1)))`.
- `ProperTimeGR.stepTime_eq_of_eq` : two chains with the same `N` and `t` have the same step time,
  whatever their spacings.
- `ProperTimeGR.elapsed_eq_zero_iff` : `n` steps take no time iff `n = 0`.
- `ProperTimeGR.elapsed_le_travelTime` : no state crosses `n` spacings in less than `n` steps.
- `ProperTimeGR.elapsed_eq_travelTime_maxCurrentState` : the maximal current state takes exactly
  `n` steps.
- `ProperTimeGR.timeCountsSteps` : the above, with the light–mass split of the maximal current
  state (`N = 2, 3` against `N ≥ 4`) and its uncertainty ratio `1 < C < √(π²/3 − 2)`.
-/

@[expose] public noncomputable section

open scoped ComplexOrder _root_.selfAdjoint
open PhyslibAlpha.ProbabilisticTheory
open InnerProductSpace UnitalPositiveLinearMap
open CondensedMatter

namespace ProperTimeGR

variable (T : TightBindingChain)

/-- The time of one step: one spacing at the speed limit. -/
def stepTime : ℝ := T.a / T.maxCurrent

/-- **The spacing cancels.** -/
theorem stepTime_eq : stepTime T = 1 / (2 * |T.t| * Real.cos (Real.pi / (T.N + 1))) := by
  unfold stepTime TightBindingChain.maxCurrent
  rw [abs_mul, abs_of_pos T.a_pos,
    show 2 * (T.a * |T.t|) * Real.cos (Real.pi / (T.N + 1)) =
      T.a * (2 * |T.t| * Real.cos (Real.pi / (T.N + 1))) by ring,
    div_mul_cancel_left₀ T.a_pos.ne', one_div]

/-- Two chains with the same number of sites and the same hopping have the same step time,
whatever their spacings. -/
theorem stepTime_eq_of_eq (T' : TightBindingChain) (hN : T.N = T'.N) (ht : T.t = T'.t) :
    stepTime T = stepTime T' := by
  rw [stepTime_eq, stepTime_eq, hN, ht]

theorem stepTime_pos (ht : T.t ≠ 0) (hN : 2 ≤ T.N) : 0 < stepTime T := by
  rw [stepTime_eq]
  have hN' : (3 : ℝ) ≤ T.N + 1 := by
    have : (2 : ℝ) ≤ T.N := by exact_mod_cast hN
    linarith
  have h1 : 0 < Real.pi / (T.N + 1) := by positivity
  have h2 : Real.pi / (T.N + 1) < Real.pi / 2 :=
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
  have hc : 0 < Real.cos (Real.pi / (T.N + 1)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h2⟩
  have := abs_pos.mpr ht
  positivity

/-- The time of `n` steps. -/
def elapsed (n : ℕ) : ℝ := n * stepTime T

/-- **No step, no time.** -/
theorem elapsed_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) (n : ℕ) :
    elapsed T n = 0 ↔ n = 0 := by
  unfold elapsed
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact_mod_cast h
    · exact absurd h (stepTime_pos T ht hN).ne'
  · rintro rfl
    simp

/-- **No state is faster than the steps.** A state with nonzero current needs at least `n` step
times to cover `n` spacings. -/
theorem elapsed_le_travelTime (ht : T.t ≠ 0)
    (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) (n : ℕ)
    (hω : 0 < |ω⟨T.currentObservable⟩|) :
    elapsed T n ≤ n * T.a / |ω⟨T.currentObservable⟩| := by
  unfold elapsed stepTime
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left T.a_pos.le hω (T.abs_expectation_current_le ht ω))
    (Nat.cast_nonneg n)

/-- **The maximal current state takes exactly `n` steps.** -/
theorem elapsed_eq_travelTime_maxCurrentState (n : ℕ) :
    elapsed T n = n * T.a / |T.maxCurrentVectorState⟨T.currentObservable⟩| := by
  rw [T.abs_expectation_current_maxCurrentState]
  unfold elapsed stepTime
  ring

/-- **Time counts steps.** The step time does not depend on the spacing; `n` steps take no time
iff `n = 0`; no state is faster and the maximal current state is exactly that fast; the maximal
current state saturates Robertson–Schrödinger exactly at `N = 2, 3`, and from `N = 4` on its
uncertainty ratio lies strictly between `1` and `√(π²/3 − 2)`. -/
theorem timeCountsSteps (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    stepTime T = 1 / (2 * |T.t| * Real.cos (Real.pi / (T.N + 1))) ∧
    (∀ n : ℕ, elapsed T n = 0 ↔ n = 0) ∧
    (∀ (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) (n : ℕ),
      0 < |ω⟨T.currentObservable⟩| → elapsed T n ≤ n * T.a / |ω⟨T.currentObservable⟩|) ∧
    (∀ n : ℕ, elapsed T n = n * T.a / |T.maxCurrentVectorState⟨T.currentObservable⟩|) ∧
    (centeredGramDefect T.maxCurrentVectorState T.openHamiltonianObservable
      T.positionObservable = 0 ↔ T.N = 2 ∨ T.N = 3) ∧
    (4 ≤ T.N → 1 < T.uncertaintyRatio ∧ T.uncertaintyRatio < √(Real.pi ^ 2 / 3 - 2)) :=
  ⟨stepTime_eq T, elapsed_eq_zero_iff T ht hN, fun ω n hω => elapsed_le_travelTime T ht ω n hω,
    elapsed_eq_travelTime_maxCurrentState T,
    T.centeredGramDefect_maxCurrentState_eq_zero_iff ht hN,
    fun h4 => ⟨T.one_lt_uncertaintyRatio ht h4,
      T.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two ht h4⟩⟩

end ProperTimeGR
