/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import ZKLib.Data.MvPolynomial.Notation
import ZKLib.Data.MvPolynomial.Interpolation

/-!
  # Multilinear Polynomials

  This is the special case of polynomial interpolation, when we consider multilinear polynomials and
  evaluation on the hypercube `σ → Fin 2`.
-/

noncomputable section

namespace MvPolynomial

open BigOperators

universe u

variable {σ : Type*} {R : Type*} [CommRing R]

instance coeFunctionFin2 : Coe (σ → Fin 2) (σ → R) where
  coe := fun vec i => vec i

def toEvalsZeroOne (p : MvPolynomial σ R) : (σ → Fin 2) → R :=
  fun x => eval (x : σ → R) p

abbrev singleEqPolynomial (r : R) (x : MvPolynomial σ R) : MvPolynomial σ R :=
  (1 - C r) * (1 - x) + C r * x

theorem singleEqPolynomial_nf (r : R) (x : MvPolynomial σ R) :
    singleEqPolynomial r x = (2 * C r - 1) * x + (1 - C r) := by
  ring_nf

theorem singleEqPolynomial_symm (r : R) (s : R) :
    (singleEqPolynomial r (C s) : MvPolynomial σ R) = singleEqPolynomial s (C r) := by ring_nf

@[simp]
theorem singleEqPolynomial_zero (x : MvPolynomial σ R) : singleEqPolynomial (0 : R) x = 1 - x := by
  unfold singleEqPolynomial ; simp

@[simp]
theorem singleEqPolynomial_one (x : MvPolynomial σ R) : singleEqPolynomial (1 : R) x = x := by
  unfold singleEqPolynomial ; simp

-- @[simp]
theorem singleEqPolynomial_zeroOne (r : Fin 2) (x : MvPolynomial σ R) :
    singleEqPolynomial (r : R) x = if r = 0 then 1 - x else x := by
  fin_cases r <;> simp

-- @[simp]
theorem singleEqPolynomial_zeroOne_C (r : Fin 2) (x : Fin 2) :
    (singleEqPolynomial (r : R) (C x) : MvPolynomial σ R) = if x = r then 1 else 0 := by
  fin_cases r <;> fin_cases x <;> simp

-- @[simp]
-- theorem singleEqPolynomial_eval_zeroOne (x : Fin n → Fin 2) (r : Fin n → Fin 2) (i : Fin n) :
--     (eval fun i => ↑↑(x i))
--     (match r i with
--     | 0 => 1 - X i
--     | 1 => X i) = 1 := by

variable [Fintype σ]

abbrev eqPolynomial (r : σ → R) : MvPolynomial (σ) R :=
  ∏ i : σ, singleEqPolynomial (r i) (X i)

theorem eqPolynomial_expanded (r : σ → R) :
    eqPolynomial r = ∏ i : σ, ((1 - C (r i)) * (1 - X i) + C (r i) * X i) := rfl

theorem eqPolynomial_symm (x : σ → R) (y : σ → R) :
    MvPolynomial.eval y (eqPolynomial x) = MvPolynomial.eval x (eqPolynomial y) := by
  simp [eqPolynomial_expanded] ; congr ; funext ; ring_nf

-- @[simp]
theorem eqPolynomial_zeroOne (r : σ → Fin 2) : (eqPolynomial r : MvPolynomial σ R) =
    ∏ i : σ, if r i = 0 then 1 - X i else X i := by
  unfold eqPolynomial ; congr ; funext i ; simp [singleEqPolynomial_zeroOne]

@[simp]
theorem eqPolynomial_eval_zeroOne (r x : σ → Fin 2) :
    eval (x : σ → R) (eqPolynomial r) = if x = r then 1 else 0 := by
  unfold eqPolynomial ; simp
  by_cases h : x = r
  · simp [h]
    have (i : Fin 2) : (1 - (i : R)) * (1 - (i : R)) + i * i = 1 := by
      fin_cases i <;> ring_nf
    simp [this]
  · simp [h]
    have : ∃ i : σ, x i ≠ r i := Function.ne_iff.mp h
    obtain ⟨i, hi⟩ := this
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    by_cases h' : r i = 0
    · simp_all [Fin.eq_one_of_neq_zero]
    · have : x i = 0 := by fin_omega
      simp_all [Fin.eq_one_of_neq_zero]

variable [DecidableEq σ]

/-- Multilinear extension of evaluations on the hypercube -/
def MLE (evals : (σ → Fin 2) → R) : MvPolynomial σ R :=
    ∑ x : σ → Fin 2, (eqPolynomial (x : σ → R)) * C (evals x)

theorem MLE_expanded (evals : (σ → Fin 2) → R) : MLE evals =
    ∑ x : σ → Fin 2, (∏ i : σ, ((1 - C (x i : R)) * (1 - X i) + C (x i : R) * X i))
      * C (evals x) := by
  unfold MLE ; congr

@[simp]
theorem MLE_eval_zeroOne (x : σ → Fin 2) (evals : (σ → Fin 2) → R) :
    MvPolynomial.eval (x : σ → R) (MLE evals) = evals x := by
  simp only [MLE, eval_sum, eval_mul, eqPolynomial_eval_zeroOne]
  simp

section DegreeOf

omit [Fintype σ] in
theorem singleEqPolynomial_degreeOf (r : R) (i j : σ) :
    degreeOf i (singleEqPolynomial r (X j)) ≤ if i = j then 1 else 0 := by
  rw [singleEqPolynomial_nf]
  calc
    _ ≤ max (degreeOf i ((2 * C r - 1) * X j)) (degreeOf i (1 - C r)) := by
      exact degreeOf_add_le i _ _
    _ ≤ max (degreeOf i (2 * C r - 1) + degreeOf i (X j))
            (degreeOf i (1 - C r)) := by
      gcongr
      repeat exact degreeOf_mul_le i _ _
    _ = max (degreeOf i (C (2 * r - 1)) + degreeOf i (X j))
            (degreeOf i (C (1 - r))) := by
      congr
      · simp only [map_sub, map_mul, map_one, sub_left_inj]; congr
      · simp only [map_sub, map_one]
    _ = max (0 + degreeOf i (X j)) 0 := by
      congr <;>
      exact degreeOf_C (R := R) _ i
    _ ≤ max (0 + (if i = j then 1 else 0)) 0 := by
      gcongr
      by_cases h : i = j
      · simp [h]; exact degreeOf_X_le j _
      · simp [h]; exact degreeOf_X_of_ne i j h
    _ = if i = j then 1 else 0 := by norm_num

theorem eqPolynomial_mem_restrictDegree (r : σ → R) : (eqPolynomial r) ∈ R⦃≤ 1⦄[X σ] := by
  simp [mem_restrictDegree_iff_degreeOf_le, eqPolynomial]
  intro i
  calc
    _ ≤ ∑ j : σ, degreeOf i (singleEqPolynomial (r j) (X j)) := by
      exact degreeOf_prod_le i _ _
    _ ≤ ∑ j : σ, if i = j then 1 else 0 := by
      gcongr
      exact singleEqPolynomial_degreeOf _ _ _
    _ = 1 := by norm_num

theorem eqPolynomial_degreeOf (r : σ → R) (i : σ) : degreeOf i (eqPolynomial r) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact eqPolynomial_mem_restrictDegree r

theorem MLE_mem_restrictDegree (evals : (σ → Fin 2) → R) : (MLE evals) ∈ R⦃≤ 1⦄[X σ] := by
  simp [mem_restrictDegree_iff_degreeOf_le, MLE]
  intro i
  calc
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i ((eqPolynomial (x : σ → R)) * C (evals x)) := by
      exact degreeOf_sum_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup
          fun x => degreeOf i (eqPolynomial (x : σ → R)) + degreeOf i (C (evals x)) := by
      gcongr
      exact degreeOf_mul_le i _ _
    _ ≤ (@Finset.univ (σ → Fin 2) _).sup fun x => 1 + 0 := by
      gcongr <;>
      simp [eqPolynomial_degreeOf]
    _ ≤ 1 := by simp

theorem MLE_degreeOf (evals : (σ → Fin 2) → R) (i : σ) : degreeOf i (MLE evals) ≤ 1 := by
  apply (mem_restrictDegree_iff_degreeOf_le _ _).mp
  exact MLE_mem_restrictDegree evals

end DegreeOf

-- TODO: add lemmas about the uniqueness of multilinear polynomials up to evaluations on hypercube

theorem is_multilinear_iff_eq_evals_zeroOne (p : MvPolynomial σ R) :
    p ∈ R⦃≤ 1⦄[X σ] ↔ p = MLE p.toEvalsZeroOne := by
  sorry

theorem is_multilinear_eq_iff_eq_evals_zeroOne (p : MvPolynomial σ R) (q : MvPolynomial σ R) :
    p ∈ R⦃≤ 1⦄[X σ] → q ∈ R⦃≤ 1⦄[X σ] → (p = q ↔ p.toEvalsZeroOne = q.toEvalsZeroOne) := by
  sorry

/-- Equivalence between multilinear polynomials and their evaluations on the Boolean hypercube -/
def MLEEquiv : R⦃≤ 1⦄[X σ] ≃ ((σ → Fin 2) → R) where
  toFun := fun p x => MvPolynomial.eval (x : σ → R) p
  invFun := fun evals => ⟨MLE evals, MLE_mem_restrictDegree evals⟩
  left_inv := fun p => by simp; ext s; sorry
  right_inv := fun evals => by simp only [MLE_eval_zeroOne]

end MvPolynomial

end
