/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.Saturation
public import Physlib.Relativity.Special.ProperTime

/-!

# The Gram defect as a Minkowski product

The centered Gram defect of two observables is the Minkowski product of a vector of `SpaceTime 3`.

## i. Overview

For a state `ω` and observables `a`, `b`, `PhyslibAlpha.ProbabilisticTheory` has the centered Gram
defect `variance a * variance b - normSq (ω (centered a * centered b))` and, in
`normSq_centered_pairing`, the squared pairing `covariance² + ⟨⁅a, b⁆⟩²`. These are the four
numbers

  `((variance a + variance b) / 2, covariance a b, ⟨⁅a, b⁆⟩, (variance a - variance b) / 2)`,

and `variance a * variance b - covariance² - ⟨⁅a, b⁆⟩²` is `v₀² - v₁² - v₂² - v₃²` for them.
This file puts them in `SpaceTime 3` and states the consequence with Physlib's own `⟪·, ·⟫ₘ`,
`causalCharacter` and `SpaceTime.properTime`. Nothing is defined except that vector.

## ii. Key results

- `centeredGramVector` : the four numbers above as a point of `SpaceTime 3`.
- `minkowskiProduct_centeredGramVector` : `⟪v, v⟫ₘ = centeredGramDefect ω a b`.
- `properTime_centeredGramVector` : `SpaceTime.properTime 0 v = √(centeredGramDefect ω a b)`.
- `causalCharacter_centeredGramVector_ne_spaceLike` : the Robertson–Schrödinger relation.
- `causalCharacter_centeredGramVector_eq_lightLike_iff` : it is an equality exactly when `v` is
  light-like.
- `causalCharacter_maxCurrentGramVector_eq_lightLike_iff` : for the maximal current state of a
  tight-binding chain, `v` is light-like exactly for `N = 2, 3`.
- `properTime_maxCurrentGramVector_pos` : and `SpaceTime.properTime v > 0` from `N = 4` on.

## iii. Table of contents

- A. The vector
- B. The tight-binding chain

## iv. References

- H. P. Robertson, *The uncertainty principle*, Phys. Rev. 34 (1929) 163.

-/

@[expose] public noncomputable section

open Lorentz Vector
open scoped ComplexOrder _root_.selfAdjoint
open PhyslibAlpha.ProbabilisticTheory UnitalPositiveLinearMap

namespace ProperTimeGR

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-!

## A. The vector

-/

/-- The vector of `SpaceTime 3` with time component `(variance a + variance b) / 2` and space
components `covariance a b`, `⟨⁅a, b⁆⟩` and `(variance a - variance b) / 2`. -/
def centeredGramVector (ω : 𝓢[ℂ, A]) (a b : Observable A) : SpaceTime 3 :=
  Sum.elim (fun _ => (variance ω a + variance ω b) / 2)
    (![covariance ω a b, ω⟨⁅a, b⁆⟩, (variance ω a - variance ω b) / 2])

/-- The Minkowski product of the vector with itself is the centered Gram defect. -/
lemma minkowskiProduct_centeredGramVector (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    ⟪centeredGramVector ω a b, centeredGramVector ω a b⟫ₘ = centeredGramDefect ω a b := by
  rw [minkowskiProduct_toCoord, centeredGramDefect, normSq_centered_pairing]
  simp [centeredGramVector, Fin.sum_univ_three]
  ring

/-- `SpaceTime.properTime` from the origin to the vector is the square root of the centered Gram
defect. -/
lemma properTime_centeredGramVector (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    SpaceTime.properTime 0 (centeredGramVector ω a b) = √(centeredGramDefect ω a b) := by
  rw [SpaceTime.properTime, sub_zero, minkowskiProduct_centeredGramVector]

/-- **Robertson–Schrödinger.** The vector is never space-like. -/
lemma causalCharacter_centeredGramVector_ne_spaceLike (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    causalCharacter (centeredGramVector ω a b) ≠ CausalCharacter.spaceLike := by
  rw [Ne, spaceLike_iff_norm_sq_neg, minkowskiProduct_centeredGramVector]
  exact not_lt.mpr (centeredGramDefect_nonneg ω a b)

/-- The Robertson–Schrödinger relation is an equality exactly when the vector is light-like. -/
lemma causalCharacter_centeredGramVector_eq_lightLike_iff (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    causalCharacter (centeredGramVector ω a b) = CausalCharacter.lightLike ↔
      covariance ω a b ^ 2 + ω⟨⁅a, b⁆⟩ ^ 2 = variance ω a * variance ω b := by
  rw [lightLike_iff_norm_sq_zero, minkowskiProduct_centeredGramVector,
    robertson_schrodinger_eq_iff_gram_zero]

/-- The Robertson–Schrödinger relation is strict exactly when the vector is time-like. -/
lemma causalCharacter_centeredGramVector_eq_timeLike_iff (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    causalCharacter (centeredGramVector ω a b) = CausalCharacter.timeLike ↔
      0 < centeredGramDefect ω a b := by
  rw [timeLike_iff_norm_sq_pos, minkowskiProduct_centeredGramVector]

/-!

## B. The tight-binding chain

-/

open CondensedMatter CondensedMatter.TightBindingChain

/-- The vector of the maximal current state of the chain, for the energy and the position. -/
def maxCurrentGramVector (T : TightBindingChain) : SpaceTime 3 :=
  centeredGramVector T.maxCurrentVectorState T.openHamiltonianObservable T.positionObservable

/-- In the maximal current state the vector is light-like exactly for `N = 2` and `N = 3`. -/
lemma causalCharacter_maxCurrentGramVector_eq_lightLike_iff (T : TightBindingChain)
    (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    causalCharacter (maxCurrentGramVector T) = CausalCharacter.lightLike ↔
      T.N = 2 ∨ T.N = 3 := by
  rw [maxCurrentGramVector, lightLike_iff_norm_sq_zero, minkowskiProduct_centeredGramVector]
  exact T.centeredGramDefect_maxCurrentState_eq_zero_iff ht hN

/-- From `N = 4` on the vector of the maximal current state is time-like. -/
lemma causalCharacter_maxCurrentGramVector_eq_timeLike (T : TightBindingChain) (ht : T.t ≠ 0)
    (hN : 4 ≤ T.N) :
    causalCharacter (maxCurrentGramVector T) = CausalCharacter.timeLike := by
  rw [maxCurrentGramVector, timeLike_iff_norm_sq_pos, minkowskiProduct_centeredGramVector]
  refine lt_of_le_of_ne (centeredGramDefect_nonneg _ _ _) fun h => ?_
  have := (T.centeredGramDefect_maxCurrentState_eq_zero_iff ht (by omega)).mp h.symm
  omega

/-- From `N = 4` on, `SpaceTime.properTime` of the vector of the maximal current state is positive
(`SpaceTime.properTime_pos_ofTimeLike`). -/
lemma properTime_maxCurrentGramVector_pos (T : TightBindingChain) (ht : T.t ≠ 0)
    (hN : 4 ≤ T.N) : 0 < SpaceTime.properTime 0 (maxCurrentGramVector T) :=
  SpaceTime.properTime_pos_ofTimeLike 0 _
    (by simpa using causalCharacter_maxCurrentGramVector_eq_timeLike T ht hN)

/-- For `N = 2, 3`, `SpaceTime.properTime` of the vector of the maximal current state is zero
(`SpaceTime.properTime_zero_ofLightLike`). -/
lemma properTime_maxCurrentGramVector_eq_zero (T : TightBindingChain) (ht : T.t ≠ 0)
    (hN : 2 ≤ T.N) (h : T.N = 2 ∨ T.N = 3) :
    SpaceTime.properTime 0 (maxCurrentGramVector T) = 0 :=
  SpaceTime.properTime_zero_ofLightLike 0 _
    (by simpa using (causalCharacter_maxCurrentGramVector_eq_lightLike_iff T ht hN).mpr h)

end ProperTimeGR
