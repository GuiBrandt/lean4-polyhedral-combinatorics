import PolyhedralCombinatorics.LinearSystem.Basic

/-!
# Linear constraints in linear systems

Although inequalities of the form `yᵀ x ≤ b` (where `y` is a coefficient vector
and `b` is a scalar) are sufficient to represent all linear systems, it is
often convenient to be able to use equalities (`yᵀ x = b`) or inequalities in
the other direction (`yᵀ x ≥ b`).

To this end, we hereby define the type of linear constraints and prove some
relevant theorems about how linear systems defined by a set of constraints
behave.

## Main definitions

* `LinearConstraint`: The type of linear constraints.
* `LinearSystem.ofConstraints`: The linear system corresponding to a list of
  constraints.

## Main results

* `LinearSystem.solutions_ofConstraints`: Characterization of the solutions of
  a linear system in terms of the constraints that define it.
-/

variable
  (𝔽 : Type*) [LinearOrderedField 𝔽] -- Field type
  (n : ℕ) -- Dimension of the space

/-- `LinearConstraint n` is the type of linear constraints on `n` variables. -/
inductive LinearConstraint (𝔽 : Type*) (n : ℕ) where
| le : (Fin n → 𝔽) → 𝔽 → LinearConstraint 𝔽 n
| eq : (Fin n → 𝔽) → 𝔽 → LinearConstraint 𝔽 n
| ge : (Fin n → 𝔽) → 𝔽 → LinearConstraint 𝔽 n

variable {𝔽 n} {y : Fin n → 𝔽} {b : 𝔽}

namespace LinearConstraint
open Matrix

/-- Whether a linear constraint is valid for a given vector. -/
@[simp] def valid : LinearConstraint 𝔽 n → (Fin n → 𝔽) → Prop
| le y b, x => y ⬝ᵥ x ≤ b
| eq y b, x => y ⬝ᵥ x = b
| ge y b, x => y ⬝ᵥ x ≥ b

lemma eq_valid_iff : (eq y b).valid x ↔ (le y b).valid x ∧ (ge y b).valid x := by
  simp [le_antisymm_iff]

end LinearConstraint

namespace LinearSystem

open LinearConstraint Matrix

/-- Constructs a linear system from a list of linear constraints. -/
def ofConstraints : List (LinearConstraint 𝔽 n) → LinearSystem 𝔽 n
  | [] => of vecEmpty vecEmpty
  | c :: cs =>
    match c with
    | le y b => cons y b $ ofConstraints cs
    | ge y b => cons (-y) (-b) $ ofConstraints cs
    | eq y b => cons y b $ cons (-y) (-b) $ ofConstraints cs

section toSet_ofConstraints
open Matrix LinearConstraint

variable {cs : List (LinearConstraint 𝔽 n)} {y : Fin n → 𝔽} {b : 𝔽}

@[simp] lemma ofConstraints_nil
  : (@ofConstraints 𝔽 _ n  []) = of vecEmpty vecEmpty := rfl

theorem mem_ofConstraints_nil_solutions : x ∈ (@ofConstraints 𝔽 _ n []).solutions := by simp

@[simp] private lemma vecCons_mulVec
  {m n : ℕ} (y : Fin n → 𝔽) (A : Matrix (Fin m) (Fin n) 𝔽) (x : Fin n → 𝔽)
  : vecCons y A *ᵥ x = vecCons (y ⬝ᵥ x) (A *ᵥ x) := by
  funext x
  cases x using Fin.cases <;> rfl

@[simp] private lemma vecCons_le_vecCons {n : ℕ} (a b : 𝔽) (x y : Fin n → 𝔽)
  : vecCons a x ≤ vecCons b y ↔ a ≤ b ∧ x ≤ y := by
  simp_rw [Pi.le_def]
  constructor <;> intro h
  . constructor
    . exact h 0
    . intro i
      exact h i.succ
  . intro i
    cases i using Fin.cases
    . simp only [cons_val_zero, h.1]
    . simp only [cons_val_succ, h.2]

@[simp] lemma mem_ofConstraints_cons_solutions
  : x ∈ (@ofConstraints 𝔽 _ n $ c :: cs).solutions ↔ c.valid x ∧ x ∈ (ofConstraints cs).solutions := by
  simp only [solutions, Set.mem_setOf_eq, valid, ge_iff_le]
  rw [ofConstraints]
  split <;> simp [le_antisymm_iff, and_assoc]

@[simp] lemma ofConstraints_le_cons
  : (ofConstraints $ le y b :: cs) = cons y b (ofConstraints cs) := by
  rfl

@[simp] lemma ofConstraints_ge_cons
  : (ofConstraints $ ge y b :: cs) = cons (-y) (-b) (ofConstraints cs) := by
  rfl

@[simp] lemma ofConstraints_eq_cons
  : (ofConstraints $ eq y b :: cs) =
    cons y b (cons (-y) (-b) $ ofConstraints cs) := by
  rfl

@[simp] theorem mem_solutions_ofConstraints (x : Fin n → 𝔽)
  : x ∈ (ofConstraints cs).solutions ↔ ∀ c ∈ cs, c.valid x := by
  induction cs
  case nil =>
    simp
  case cons c cs ih =>
    simp only [mem_ofConstraints_cons_solutions, List.forall_mem_cons, ih]

/-- The set of solutions of a linear system of constraints is the set of all points that satisfy
  all constraints. -/
@[simp] theorem solutions_ofConstraints
  : (ofConstraints cs).solutions = { x : Fin n → 𝔽 | ∀ c ∈ cs, c.valid x } :=
  Set.ext_iff.mpr mem_solutions_ofConstraints

end toSet_ofConstraints

end LinearSystem
