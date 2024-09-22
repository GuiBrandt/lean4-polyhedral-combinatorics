import PolyhedralCombinatorics.Projection.Computable

import PolyhedralCombinatorics.Polyhedron.Notation

variable {𝔽} [lof : LinearOrderedField 𝔽] {n : ℕ}

namespace LinearSystem
open Matrix

def elim0 (S : LinearSystem 𝔽 (n + 1)) : LinearSystem 𝔽 n :=
  LinearSystem.of (vecTail ∘ S.mat) S.vec

theorem mem_elim0_of_vecCons_zero_mem {S : LinearSystem 𝔽 (n + 1)} {x : Fin n → 𝔽}
  (h : vecCons 0 x ∈ S.solutions) : x ∈ S.elim0.solutions := by
  simp only [elim0, mem_solutions, Pi.le_def, mulVec, of_apply] at h ⊢
  intro i
  replace h := h i
  rw [dotProduct_cons, mul_zero, zero_add] at h
  exact h

end LinearSystem

namespace Polyhedron
open Matrix

def fourierMotzkin (P : Polyhedron 𝔽 n) (j : Fin n) :=
  !P{x_[j] = 0} ∩ P.computeProjection x_[j]

theorem mem_fourierMotzkin (P : Polyhedron 𝔽 n) (j : Fin n) :
  x ∈ P.fourierMotzkin j ↔ x j = 0 ∧ ∃ (α : 𝔽), x + Pi.single j α ∈ P := by
  simp_rw [
    fourierMotzkin, mem_inter, mem_computeProjection, mem_ofConstraints,
    List.mem_singleton, forall_eq, LinearConstraint.valid,
    single_dotProduct, one_mul, and_congr_right_iff,
    ←Pi.single_smul, smul_eq_mul, mul_one, implies_true
  ]

-- def elimSucc (P : Polyhedron 𝔽 (n + 1)) : Polyhedron 𝔽 n :=
--   Quotient.recOn P
--     (fun S ↦ LinearSystem.of (Matrix.of fun i j ↦ S.mat i j.castSucc) S.vec)
--     fun S S' h ↦ by
--       ext x
--       simp only [eq_rec_constant, mem_ofLinearSystem_of]
--       simp_rw [LinearSystem.equiv_def, Set.ext_iff, LinearSystem.mem_solutions] at h
--       replace h := h $ fun i ↦ if h : i.val < n then x (i.castLT h) else 0
--       simp_rw [Pi.le_def, mulVec] at h
--       sorry

-- def recElimDimensions (p : Polyhedron 𝔽 n) {k : ℕ} (h : k ≤ n) :=
--   match k with
--   | 0 => p
--   | k + 1 => (p.recElimDimensions $ le_of_add_le_left h).computeProjection x_[⟨k, h⟩]

-- @[simp] theorem recElimDimensions_eq_empty_iff (p : Polyhedron 𝔽 n) {k : ℕ} (hk : k ≤ n)
--   : p.recElimDimensions hk = ∅ ↔ p = ∅ := by
--   unfold recElimDimensions
--   split
--   . rfl
--   . rw [computeProjection_eq_empty_iff]
--     apply p.recElimDimensions_eq_empty_iff

-- theorem recElimDimensions_all_empty_or_univ (p : Polyhedron 𝔽 n) {k : ℕ}
--   : let p' := p.recElimDimensions (le_refl _); p' = ∅ ∨ p' = ⊤ := by
--   unfold recElimDimensions
--   split
--   . by_cases finZeroElim ∈ p <;> simp_all [Polyhedron.ext_iff, not_mem_empty, mem_univ]
--   . simp only [Nat.succ_eq_add_one, computeProjection_eq_empty_iff, recElimDimensions_eq_empty_iff]
--     by_cases p = ∅
--     . left; assumption
--     . right
--       simp_rw [Polyhedron.ext_iff, mem_computeProjection, mem_univ, iff_true]
--       intro x
--       sorry
