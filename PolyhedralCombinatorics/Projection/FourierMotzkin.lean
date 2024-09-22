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

def fourierMotzkin (S : LinearSystem 𝔽 n) (j : Fin n) :=
  !L{x_[j] = 0} ++ S.computeProjection x_[j]

theorem mem_fourierMotzkin  {S : LinearSystem 𝔽 n} {j : Fin n} :
  x ∈ (S.fourierMotzkin j).solutions ↔ x j = 0 ∧ ∃ (α : 𝔽), x + Pi.single j α ∈ S.solutions := by
  simp_rw [
    fourierMotzkin, mem_concat, mem_computeProjection, mem_ofConstraints,
    List.mem_singleton, forall_eq, LinearConstraint.valid,
    single_dotProduct, one_mul, and_congr_right_iff, mem_projection,
    ←Pi.single_smul, smul_eq_mul, mul_one, implies_true
  ]

def fourierMotzkinElim0 (S : LinearSystem 𝔽 (n + 1)) : LinearSystem 𝔽 n :=
  (S.fourierMotzkin 0).elim0

theorem mem_fourierMotzkinElim0 {S : LinearSystem 𝔽 (n + 1)} {x : Fin n → 𝔽}
  : x ∈ S.fourierMotzkinElim0.solutions ↔ ∃ x₀ : 𝔽, vecCons x₀ x ∈ S.solutions := by
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

theorem fourierMotzkinElim0_eq_empty_iff {S : LinearSystem 𝔽 (n + 1)}
  : S.fourierMotzkinElim0.solutions = ∅ ↔ S.solutions = ∅ := by
  simp_rw [Set.eq_empty_iff_forall_not_mem, mem_fourierMotzkinElim0, not_exists]
  constructor <;> intro h x
  . rw [←Matrix.cons_head_tail x]
    apply h
  . intros
    apply h

def fourierMotzkinElimRec {n : ℕ} (S : LinearSystem 𝔽 n) : LinearSystem 𝔽 0 :=
  match n with
  | 0 => S
  | _ + 1 => fourierMotzkinElimRec S.fourierMotzkinElim0

@[simp] theorem recElimDimensions_eq_empty_iff (S : LinearSystem 𝔽 n)
  : S.fourierMotzkinElimRec.solutions = ∅ ↔ S.solutions = ∅ := by
  induction n
  case zero => rfl
  case succ n ih =>
    transitivity
    . apply ih
    . exact S.fourierMotzkinElim0_eq_empty_iff

end LinearSystem
