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

inductive LinearConstraint.Comparator | le | eq | ge

/-- `LinearConstraint n` is the type of linear constraints on `n` variables. -/
structure LinearConstraint where
  coefficients : Fin n → 𝔽
  comparator : LinearConstraint.Comparator
  rhs : 𝔽

variable {𝔽 n} {y : Fin n → 𝔽} {b : 𝔽}

namespace LinearConstraint
open Matrix

@[match_pattern] abbrev le (y : Fin n → 𝔽) (b : 𝔽) : LinearConstraint 𝔽 n := ⟨y, .le, b⟩
@[match_pattern] abbrev eq (y : Fin n → 𝔽) (b : 𝔽) : LinearConstraint 𝔽 n := ⟨y, .eq, b⟩
@[match_pattern] abbrev ge (y : Fin n → 𝔽) (b : 𝔽) : LinearConstraint 𝔽 n := ⟨y, .ge, b⟩

/-- Converts a linear constraint into a list o extended matrix rows for a
  linear system. -/
def toExtendedRows : LinearConstraint 𝔽 n → List ((Fin n → 𝔽) × 𝔽)
| le y b => [(y, b)]
| eq y b => [(y, b), (-y, -b)]
| ge y b => [(-y, -b)]

@[simp] lemma le_toExtendedRows : toExtendedRows (le y b) = [(y, b)] := rfl
@[simp] lemma eq_toExtendedRows : toExtendedRows (eq y b) = [(y, b), (-y, -b)] := rfl
@[simp] lemma ge_toExtendedRows : toExtendedRows (ge y b) = [(-y, -b)] := rfl

def Comparator.valid : Comparator → 𝔽 → 𝔽 → Prop
| le => (· ≤ ·) | eq => (· = ·) | ge => (· ≥ ·)

/-- Whether a linear constraint is valid for a given vector. -/
def valid : LinearConstraint 𝔽 n → (Fin n → 𝔽) → Prop
| ⟨y, cmp, b⟩, x => cmp.valid (y ⬝ᵥ x) b

@[simp] lemma le_valid : (le y b).valid x = (y ⬝ᵥ x ≤ b) := rfl
@[simp] lemma eq_valid : (eq y b).valid x = (y ⬝ᵥ x = b) := rfl
@[simp] lemma ge_valid : (ge y b).valid x = (y ⬝ᵥ x ≥ b) := rfl

lemma eq_valid_iff : (eq y b).valid x ↔ (le y b).valid x ∧ (ge y b).valid x := by
  simp [le_antisymm_iff]

end LinearConstraint

namespace LinearSystem

open LinearConstraint

/-- Constructs a linear system from a list of linear constraints. -/
def ofConstraints (cs : List (LinearConstraint 𝔽 n)) : LinearSystem 𝔽 n :=
  let rows := cs.bind toExtendedRows
  ⟨rows.length, Matrix.of (Prod.fst ∘ rows.get), Prod.snd ∘ rows.get⟩

section toSet_ofConstraints
open Matrix LinearConstraint

variable {cs : List (LinearConstraint 𝔽 n)} {y : Fin n → 𝔽} {b : 𝔽}

@[simp]
lemma ofConstraints_mat_apply : (ofConstraints cs).mat i = (cs.bind toExtendedRows)[i].1 := rfl

@[simp]
lemma ofConstraints_vec_apply : (ofConstraints cs).vec i = (cs.bind toExtendedRows)[i].2 := rfl

@[simp] lemma ofConstraints_apply_eq_lemma
  : let s := ofConstraints cs
    s.mat i = y ∧ s.vec i = b ↔ (cs.bind toExtendedRows)[i] = (y, b) := by
  simp only [ofConstraints_mat_apply, ofConstraints_vec_apply]
  apply Prod.mk.inj_iff.symm

macro "linear_constraint_lemma_tac" h:ident : tactic =>
  `(tactic|
    simp_rw [ofConstraints_apply_eq_lemma]
    <;> exact List.mem_iff_get.mp $ List.mem_bind.mpr ⟨_, $h, by simp [toExtendedRows]⟩)

private lemma le_lemma (h : ⟨y, Comparator.le, b⟩ ∈ cs)
  : let s := ofConstraints cs; ∃ i, s.mat i = y ∧ s.vec i = b := by
  linear_constraint_lemma_tac h

private lemma ge_lemma (h : ⟨y, Comparator.ge, b⟩ ∈ cs)
  : let s := ofConstraints cs; ∃ i, -(s.mat i) = y ∧ -(s.vec i) = b := by
  simp_rw [neg_eq_iff_eq_neg]
  linear_constraint_lemma_tac h

private lemma eq_lemma (h : ⟨y, Comparator.eq, b⟩ ∈ cs)
  : let s := ofConstraints cs;
    (∃ i, s.mat i = y ∧ s.vec i = b) ∧ (∃ i, -(s.mat i) = y ∧ -(s.vec i) = b) := by
  simp_rw [neg_eq_iff_eq_neg]
  constructor <;> linear_constraint_lemma_tac h

@[simp] theorem mem_solutions_ofConstraints (x : Fin n → 𝔽)
  : x ∈ (ofConstraints cs).solutions ↔ ∀ c ∈ cs, c.valid x := by
  let rows := cs.bind toExtendedRows
  constructor
  . show x ∈ (ofConstraints cs).solutions → ∀ c ∈ cs, c.valid _
    intro h ⟨y, cmp, b⟩ mem_cs
    cases cmp
    case' le => have ⟨_, hy, hb⟩ := le_lemma mem_cs
    case' ge => have ⟨_, hy, hb⟩ := ge_lemma mem_cs
    case' eq =>
      rw [eq_valid_iff]
      constructor
      case' left => have ⟨_, hy, hb⟩ := (eq_lemma mem_cs).1
      case' right => have ⟨_, hy, hb⟩ := (eq_lemma mem_cs).2
    all_goals subst hy hb
    case le | eq.left =>
      apply h
    case ge | eq.right =>
      simp_rw [ge_valid, neg_dotProduct, neg_le_neg_iff]
      apply h
  . show (∀ c ∈ cs, c.valid x) → ∀ (i : Fin rows.length), rows[i].1 ⬝ᵥ _ ≤ rows[i].2
    intro h i
    have : rows[i] ∈ rows := List.get_mem rows i i.prop
    have ⟨⟨y, cmp, b⟩, mem_cs, h'⟩ := List.mem_bind.mp this
    have c_valid := h _ mem_cs
    cases cmp
    case' eq =>
      rw [eq_valid_iff] at c_valid
      rw [toExtendedRows, List.mem_pair] at h'
      cases h'
    case le | eq.inl =>
      rw [le_valid] at c_valid
      simp_all only [toExtendedRows, List.mem_singleton]
    case ge | eq.inr =>
      rw [ge_valid] at c_valid
      simp_all only [toExtendedRows, List.mem_singleton, neg_dotProduct, neg_le_neg_iff]

/-- The set of solutions of a linear system of constraints is the set of all points that satisfy
  all constraints. -/
@[simp] theorem solutions_ofConstraints
  : (ofConstraints cs).solutions = { x : Fin n → 𝔽 | ∀ c ∈ cs, c.valid x } :=
  Set.ext_iff.mpr mem_solutions_ofConstraints

end toSet_ofConstraints

end LinearSystem
