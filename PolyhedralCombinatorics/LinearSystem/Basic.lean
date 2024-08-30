import PolyhedralCombinatorics.LinearSystem.Defs

import Mathlib.Analysis.Convex.Basic

/-!
# Theorems about linear systems

This file contains theorems about linear systems.

## Main results

* `LinearSystem.solutions_concat`: Characterizes the set of solutions of the
  concatenation of two linear systems.
* `LinearSystem.solutions_convex`: The set of solutions of a linear system is convex.
-/

namespace LinearSystem
open Matrix

variable {𝔽 n} [LinearOrderedField 𝔽] (p q : LinearSystem 𝔽 n)

open Matrix

@[simp] lemma mem_solutions : x ∈ p.solutions ↔ p.mat *ᵥ x ≤ p.vec := Set.mem_setOf

@[simp] lemma mem_solutions_of {x : Fin n → 𝔽} : x ∈ (of A b).solutions ↔ A *ᵥ x ≤ b := Set.mem_setOf

/-- The set of solutions of the concatenation of two linear systems is the intersection of their
  sets of solutions. -/
@[simp] theorem solutions_concat : (p.concat q).solutions = p.solutions ∩ q.solutions := by
  simp_rw [Set.ext_iff, Set.mem_inter_iff]
  intro x
  constructor <;> intro h
  . simp_rw [concat, mem_solutions, Pi.le_def] at h
    constructor <;> (rw [mem_solutions, Pi.le_def]; intro i)
    . have := h (i.castLE $ Nat.le_add_right ..)
      simp_all [mulVec]
    . have := h ⟨p.m + i, Nat.add_lt_add_left i.prop ..⟩
      simp_all [mulVec]
  . simp_rw [concat, mem_solutions, Pi.le_def]
    intro i
    by_cases hi : i < p.m <;> simp only [hi, mulVec, ↓reduceDIte, of_apply]
    . apply h.1
    . apply h.2

/-- The set of solutions of a linear system is convex. -/
theorem solutions_convex : Convex 𝔽 p.solutions := by
  intro x x_mem_p y y_mem_p α β α_nonneg β_nonneg αβ_affine
  calc
    p.mat *ᵥ (α • x + β • y) = α • p.mat *ᵥ x + β • p.mat *ᵥ y := by
      simp_rw [mulVec_add, mulVec_smul]
    _ ≤ α • p.vec + β • p.vec :=
      add_le_add
        (smul_le_smul_of_nonneg_left x_mem_p α_nonneg)
        (smul_le_smul_of_nonneg_left y_mem_p β_nonneg)
    _ = p.vec := by rw [←add_smul, αβ_affine, one_smul]
