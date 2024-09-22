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

theorem mem_elim0 {S : LinearSystem 𝔽 (n + 1)} {x : Fin n → 𝔽}
  : x ∈ S.elim0.solutions ↔ vecCons 0 x ∈ S.solutions := by
  simp only [elim0, mem_solutions, Pi.le_def]
  apply forall_congr'
  intro i
  simp_rw [mulVec, Function.comp_apply, dotProduct_cons, mul_zero, zero_add]

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

def elim0 (P : Polyhedron 𝔽 (n + 1)) : Polyhedron 𝔽 n :=
  Quotient.recOn P (Polyhedron.ofLinearSystem ∘ LinearSystem.elim0)
    fun S S' heq ↦ by
      ext x
      simp_rw [LinearSystem.equiv_def, Set.ext_iff] at heq
      simp only [eq_rec_constant, Function.comp_apply, mem_ofLinearSystem, LinearSystem.mem_elim0]
      apply heq

theorem mem_elim0 {P : Polyhedron 𝔽 (n + 1)} {x : Fin n → 𝔽}
  : x ∈ P.elim0 ↔ vecCons 0 x ∈ P :=
  Quotient.recOn P (fun S ↦ S.mem_elim0) (fun _ _ _ ↦ rfl)

def fourierMotzkinElim0 (P : Polyhedron 𝔽 (n + 1)) : Polyhedron 𝔽 n :=
  (P.fourierMotzkin 0).elim0

theorem mem_fourierMotzkinElim0 {P : Polyhedron 𝔽 (n + 1)} {x : Fin n → 𝔽}
  : x ∈ P.fourierMotzkinElim0 ↔ ∃ x₀ : 𝔽, vecCons x₀ x ∈ P := by
  unfold fourierMotzkinElim0
  suffices ∀ α, (Pi.single 0 α : Fin (n + 1) → 𝔽) = vecCons α 0 by
    simp_rw [mem_elim0, mem_fourierMotzkin, cons_val_zero, true_and, cons_add,
      zero_add, vecHead, Pi.single_eq_same, this, Matrix.tail_cons, add_zero]
  intro α
  funext i
  cases i using Fin.cases
  . simp only [Pi.single_eq_same, cons_val_zero]
  . simp_rw [Pi.single_eq_of_ne (f := fun _ ↦ 𝔽) (Fin.succ_ne_zero _) _, cons_val_succ,
      Pi.zero_apply]

theorem fourierMotzkinElim0_eq_empty_iff {P : Polyhedron 𝔽 (n + 1)}
  : P.fourierMotzkinElim0 = ∅ ↔ P = ∅ := by
  simp_rw [eq_empty_iff, mem_fourierMotzkinElim0, not_exists]
  constructor <;> intro h x
  . rw [←Matrix.cons_head_tail x]
    apply h
  . intros
    apply h

def fourierMotzkinElimRec {n : ℕ} (P : Polyhedron 𝔽 n) : Polyhedron 𝔽 0 :=
  match n with
  | 0 => P
  | _ + 1 => fourierMotzkinElimRec P.fourierMotzkinElim0

@[simp] theorem recElimDimensions_eq_empty_iff (P : Polyhedron 𝔽 n)
  : P.fourierMotzkinElimRec = ∅ ↔ P = ∅ := by
  induction n
  case zero => rfl
  case succ n ih =>
    transitivity
    . apply ih
    . exact P.fourierMotzkinElim0_eq_empty_iff
