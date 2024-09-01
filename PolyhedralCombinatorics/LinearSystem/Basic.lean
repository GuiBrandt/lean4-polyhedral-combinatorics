import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Basic

/-!
# Linear systems

This file defines basic properties of linear systems.

Linear systems of `n` variables over a linear ordered field `𝔽` are represented
with `LinearSystem 𝔽 n`.

## Main definitions

* `LinearSystem`: The type of linear systems.
* `LinearSystem.of`: The linear system defined by a `m × n` coefficient matrix
  and an `m × 1` column vector.
* `LinearSystem.concat`: Concatenation of linear systems.
* `LinearSystem.solutions`: Set of solutions of a linear system.

## Main results

* `LinearSystem.solutions_concat`: Characterizes the set of solutions of the
  concatenation of two linear systems.
* `LinearSystem.solutions_convex`: The set of solutions of a linear system is convex.
-/

variable
  (𝔽 : Type*) -- Field type
  (n : ℕ) -- Dimension of the space

/-- `LinearSystem 𝔽 n` is the type of linear systems of inequalities in `𝔽^n`, where `𝔽` is a
  linear ordered field. -/
structure LinearSystem where
  /-- Number of inequalities in the system. -/
  m : ℕ
  /-- Coefficient matrix of the system. -/
  mat : Matrix (Fin m) (Fin n) 𝔽
  /-- Column-vector of the system's right-hand side. -/
  vec : Fin m → 𝔽

namespace LinearSystem
open Matrix

variable {𝔽 m n}

/-- Constructs a linear system defined by a `m × n` coefficient matrix `A` and an `m × 1` column
  vector `b`. -/
@[match_pattern] abbrev of (A : Matrix (Fin m) (Fin n) 𝔽) (b : Fin m → 𝔽) : LinearSystem 𝔽 n :=
  ⟨m, A, b⟩

def empty : LinearSystem 𝔽 n := of vecEmpty vecEmpty

/-- Prepends a linear inequality `yᵀ x ≤ b` to a linear system `p`. -/
def cons (y : Fin n → 𝔽) (b : 𝔽) (p : LinearSystem 𝔽 n) : LinearSystem 𝔽 n :=
  of (vecCons y p.mat) (vecCons b p.vec)

@[simp] lemma cons_m : (cons y b p : LinearSystem 𝔽 n).m = p.m + 1 := rfl

@[simp] lemma cons_mat : (cons y b p : LinearSystem 𝔽 n).mat = vecCons y p.mat := rfl

@[simp] lemma cons_vec : (cons y b p : LinearSystem 𝔽 n).vec = vecCons b p.vec := rfl

@[elab_as_elim] def induction {motive : LinearSystem 𝔽 n → Sort _}
  (empty : motive empty) (cons : ∀ y b p, motive p → motive (cons y b p)) : ∀ p, motive p
  | ⟨m, A, b⟩ => by
    induction m
    case zero =>
      have : A = vecEmpty := by funext x; exact Fin.elim0 x
      have : b = vecEmpty := by funext x; exact Fin.elim0 x
      subst A b
      exact empty
    case succ m ih =>
      have : ⟨_, A, b⟩ = LinearSystem.cons (vecHead A) (vecHead b) (of (vecTail A) (vecTail b)) := by
        simp only [LinearSystem.cons, Matrix.cons_head_tail]
      simp_rw [this]
      apply cons
      apply ih

@[elab_as_elim] def inductionOn {motive : LinearSystem 𝔽 n → Sort _}
  (p : LinearSystem 𝔽 n) (empty : motive empty) (cons : ∀ y b p, motive p → motive (cons y b p))
  : motive p := induction empty cons p

@[elab_as_elim] def cases {motive : LinearSystem 𝔽 n → Sort _}
  (empty : motive empty) (cons : ∀ y b p, motive (cons y b p))
  : ∀ p, motive p := induction empty fun y b p _ => cons y b p

/-- The concatenation of two linear systems. -/
def concat (p q : LinearSystem 𝔽 n) : LinearSystem 𝔽 n :=
  {
    m := p.m + q.m,
    mat := Matrix.of fun i j ↦
      if h : i < p.m then
        p.mat ⟨i, h⟩ j
      else
        q.mat ⟨i - p.m, Nat.sub_lt_left_of_lt_add (not_lt.mp h) i.prop⟩ j
    vec := fun i ↦
      if h : i < p.m then
        p.vec ⟨i, h⟩
      else
        q.vec ⟨i - p.m, Nat.sub_lt_left_of_lt_add (not_lt.mp h) i.prop⟩
  }

variable [LinearOrderedField 𝔽] (p : LinearSystem 𝔽 n)

/-- The set of solutions of the linear system. -/
@[simp] def solutions : Set (Fin n → 𝔽) := { x | p.mat *ᵥ x ≤ p.vec }

/-- Two linear systems are said to be equivalent when their sets of solutions are equal. -/
instance : HasEquiv (LinearSystem 𝔽 n) := ⟨(·.solutions = ·.solutions)⟩

instance isSetoid (𝔽 n) [LinearOrderedField 𝔽] : Setoid (LinearSystem 𝔽 n) :=
  ⟨instHasEquiv.Equiv, fun _ ↦ rfl, Eq.symm, Eq.trans⟩

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
