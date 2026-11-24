/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License 1.0.0 as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez, José Arturo Nava-Hernández
-/
module

public import ProperTimeGeneralRelativity.StepTime
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PhyslibAlpha.CondensedMatter.TightBindingChain.Open.Basic

/-!
# The step time is set by the path graph

On the open chain the Hamiltonian is `E₀ I − t A(P_N)` (Physlib #2096,
`inner_openHamiltonian_eq_adjMatrix`). The vector `v m = sin ((m + 1) π / (N + 1))` is an
eigenvector of the adjacency matrix `A(P_N)` with eigenvalue `λ = 2 cos (π / (N + 1))`. The speed
limit is `maxCurrent = |a t| λ`, and one step lasts `1 / (|t| λ)`: the spacing cancels and the step
time is fixed by `t` and the spectrum of the path graph.

## Main results

- `ProperTimeGR.adjMatrix_pathGraph_mulVec_sin` : `A(P_N) v = 2 cos (π / (N + 1)) • v`.
- `ProperTimeGR.openHamiltonian_mulVec_sin` : in the site basis, `H v = (E₀ − t λ) v`.
- `ProperTimeGR.maxCurrent_eq_pathEigenvalue` : `maxCurrent = |a t| λ`.
- `ProperTimeGR.stepTime_eq_pathEigenvalue` : `τ_pas = 1 / (|t| λ)`.
-/

@[expose] public noncomputable section

open Real CondensedMatter Matrix
open scoped InnerProductSpace CondensedMatter.TightBindingChain

namespace ProperTimeGR

/-- The vector `m ↦ sin ((m + 1) π / (N + 1))` on the sites of the path graph `P_N`. -/
def sinVector (N : ℕ) (m : Fin N) : ℝ := sin (((m : ℕ) + 1 : ℝ) * (π / (N + 1)))

/-- The eigenvalue `2 cos (π / (N + 1))` of the adjacency matrix of the path graph `P_N`. -/
def pathEigenvalue (N : ℕ) : ℝ := 2 * cos (π / (N + 1))

private lemma sin_sub_add (x θ : ℝ) : sin (x - θ) + sin (x + θ) = 2 * cos θ * sin x := by
  rw [sin_sub, sin_add]
  ring

/-- `sin ((m + 1) π / (N + 1))` is an eigenvector of the adjacency matrix of the path graph
`P_N`, with eigenvalue `2 cos (π / (N + 1))`. -/
lemma adjMatrix_pathGraph_mulVec_sin (N : ℕ) :
    (SimpleGraph.pathGraph N).adjMatrix ℝ *ᵥ sinVector N = pathEigenvalue N • sinVector N := by
  funext m
  let θ := π / (N + 1)
  let f : ℕ → ℝ := fun k => sin (k * θ)
  have hf0 : f 0 = 0 := by simp [f]
  have hfN : f (N + 1) = 0 := by
    simp only [f, θ]
    rw [show ((N + 1 : ℕ) : ℝ) * (π / (N + 1)) = π by field_simp; push_cast; ring]
    exact sin_pi
  have hv (j : Fin N) : sinVector N j = f ((j : ℕ) + 1) := by simp [sinVector, f, θ]
  simp only [mulVec, dotProduct, SimpleGraph.adjMatrix_apply, SimpleGraph.pathGraph_adj,
    Pi.smul_apply, smul_eq_mul, hv, ite_mul, one_mul, zero_mul]
  rw [Fin.sum_univ_eq_sum_range (fun j => if (m : ℕ) + 1 = j ∨ j + 1 = (m : ℕ) then f (j + 1)
    else 0)]
  have hsplit : ∀ j ∈ Finset.range N, (if (m : ℕ) + 1 = j ∨ j + 1 = (m : ℕ) then f (j + 1)
      else 0) = (if j = (m : ℕ) + 1 then f (j + 1) else 0) +
        (if j + 1 = (m : ℕ) then f (j + 1) else 0) := by
    intro j _
    by_cases h1 : j = (m : ℕ) + 1
    · simp [h1, show ¬ ((m : ℕ) + 1 + 1 = (m : ℕ)) by omega]
    · by_cases h2 : j + 1 = (m : ℕ)
      · simp [h2, h1]
      · simp [h1, h2, eq_comm (a := (m : ℕ) + 1)]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hm := m.isLt
  have hup : (if (m : ℕ) + 1 ∈ Finset.range N then f ((m : ℕ) + 1 + 1) else 0) =
      f ((m : ℕ) + 2) := by
    split_ifs with h
    · rfl
    · have : (m : ℕ) + 2 = N + 1 := by simp at h; omega
      rw [this, hfN]
  have hdown : (∑ j ∈ Finset.range N, if j + 1 = (m : ℕ) then f (j + 1) else 0) = f m := by
    rcases Nat.eq_zero_or_eq_succ_pred (m : ℕ) with h0 | hs
    · rw [h0, hf0]
      exact Finset.sum_eq_zero fun j _ => by simp
    · rw [Finset.sum_eq_single ((m : ℕ) - 1)]
      · simp only [show (m : ℕ) - 1 + 1 = m by omega, ite_true]
      · intro j _ hj
        rw [ite_eq_right_iff.mpr fun h => absurd h (by omega)]
      · intro h
        simp at h
        omega
  rw [hup, hdown]
  simp only [f, pathEigenvalue]
  have := sin_sub_add (((m : ℕ) + 1 : ℝ) * θ) θ
  push_cast
  rw [add_comm, ← this]
  congr 1 <;> ring_nf

/-- The open Hamiltonian in the site basis, `⟨m|H|n⟩`. -/
def openHamiltonianMatrix (T : TightBindingChain) : Matrix (Fin T.N) (Fin T.N) ℂ :=
  Matrix.of fun m n => ⟪|m⟩, T.openHamiltonian |n⟩⟫_ℂ

/-- Through #2096, `sin ((m + 1) π / (N + 1))` is an eigenvector of the open Hamiltonian with
energy `E₀ − t · 2 cos (π / (N + 1))`. -/
lemma openHamiltonian_mulVec_sin (T : TightBindingChain) :
    openHamiltonianMatrix T *ᵥ (fun m => (sinVector T.N m : ℂ)) =
      ((T.E0 - T.t * pathEigenvalue T.N : ℝ) : ℂ) • fun m => (sinVector T.N m : ℂ) := by
  have hH : openHamiltonianMatrix T =
      (T.E0 : ℂ) • 1 - (T.t : ℂ) • (SimpleGraph.pathGraph T.N).adjMatrix ℂ := by
    ext m n
    rw [openHamiltonianMatrix, Matrix.of_apply, T.inner_openHamiltonian_eq_adjMatrix]
    simp
  have hA : (SimpleGraph.pathGraph T.N).adjMatrix ℂ *ᵥ (fun m => (sinVector T.N m : ℂ)) =
      fun m => ((pathEigenvalue T.N * sinVector T.N m : ℝ) : ℂ) := by
    have hmap : (SimpleGraph.pathGraph T.N).adjMatrix ℂ =
        ((SimpleGraph.pathGraph T.N).adjMatrix ℝ).map Complex.ofRealHom := by
      ext i j
      by_cases h : (SimpleGraph.pathGraph T.N).Adj i j <;> simp [SimpleGraph.adjMatrix_apply, h]
    funext m
    have := RingHom.map_mulVec Complex.ofRealHom
      ((SimpleGraph.pathGraph T.N).adjMatrix ℝ) (sinVector T.N) m
    rw [adjMatrix_pathGraph_mulVec_sin] at this
    rw [hmap]
    simpa [Function.comp_def] using this.symm
  rw [hH, sub_mulVec, smul_mulVec, smul_mulVec, one_mulVec, hA]
  funext m
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The speed limit of the open chain is `|a t|` times the eigenvalue `2 cos (π / (N + 1))` of the
path graph. -/
lemma maxCurrent_eq_pathEigenvalue (T : TightBindingChain) :
    T.maxCurrent = |T.a * T.t| * pathEigenvalue T.N := by
  rw [TightBindingChain.maxCurrent, pathEigenvalue]
  ring

/-- **The step time is set by the path graph.** One step lasts `1 / (|t| · 2 cos (π / (N + 1)))`,
the inverse of `|t|` times the eigenvalue of `A(P_N)`. -/
lemma stepTime_eq_pathEigenvalue (T : TightBindingChain) :
    stepTime T = 1 / (|T.t| * pathEigenvalue T.N) := by
  rw [stepTime_eq, pathEigenvalue]
  ring_nf

end ProperTimeGR
