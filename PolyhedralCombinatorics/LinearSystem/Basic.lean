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

/-- The empty linear system. -/
@[simp] def empty : LinearSystem 𝔽 n := of vecEmpty vecEmpty

/-- A linear system is empty if and only if it has no rows. -/
theorem eq_empty_iff : p = empty ↔ p.m = 0 := by
  constructor <;> intro h
  . rw [h]
    rfl
  . obtain ⟨m, A, b⟩ := p
    simp only at h
    subst m
    suffices A = ![] ∧ b = ![] by
      rw [this.1, this.2]
      rfl
    constructor
    . funext x; apply Fin.elim0 x
    . funext x; apply Fin.elim0 x

/-- Prepends a linear inequality `yᵀ x ≤ b` to a linear system `p`. -/
@[simp] def cons (y : Fin n → 𝔽) (b : 𝔽) (p : LinearSystem 𝔽 n) : LinearSystem 𝔽 n :=
  of (vecCons y p.mat) (vecCons b p.vec)

/-- Define `motive p` by induction on `LinearSystem 𝔽 n` via induction on the inequalities of the
  system.

  This function has two arguments: `empty` gives the base case on an empty linear system, and
  `cons` gives the inductive step for a linear system of the form `cons y b p`. -/
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

/-- A version of `LinearSystem.induction` taking `p : LinearSystem 𝔽 n` as the first argument. -/
@[elab_as_elim] def inductionOn {motive : LinearSystem 𝔽 n → Sort _}
  (p : LinearSystem 𝔽 n) (empty : motive empty) (cons : ∀ y b p, motive p → motive (cons y b p))
  : motive p := induction empty cons p

/-- Define `motive p` by separately handling the cases `p = empty` and `p = cons y b q`. --/
@[elab_as_elim] def cases {motive : LinearSystem 𝔽 n → Sort _}
  (empty : motive empty) (cons : ∀ y b p, motive (cons y b p))
  : ∀ p, motive p := induction empty fun y b p _ => cons y b p

@[simp] theorem cases_empty {motive : LinearSystem 𝔽 n → Sort _}
  {empty : motive empty} {cons : ∀ y b p, motive (cons y b p)}
  : cases empty cons LinearSystem.empty = empty := rfl

@[simp] theorem cases_cons {motive : LinearSystem 𝔽 n → Sort _}
  {empty : motive empty} {cons : ∀ y b p, motive (cons y b p)}
  : cases empty cons (LinearSystem.cons y b p) = cons y b p := rfl

/-- The concatenation of two linear systems. -/
def concat (p q : LinearSystem 𝔽 n) : LinearSystem 𝔽 n :=
  {
    m := p.m + q.m,
    mat := Fin.append p.mat q.mat
    vec := Fin.append p.vec q.vec
  }

instance : Append (LinearSystem 𝔽 n) := ⟨concat⟩

theorem concat_m {p q : LinearSystem 𝔽 n} : (p ++ q).m = p.m + q.m := rfl
theorem concat_mat {p q : LinearSystem 𝔽 n} : (p ++ q).mat = Fin.append p.mat q.mat := rfl
theorem concat_vec {p q : LinearSystem 𝔽 n} : (p ++ q).vec = Fin.append p.vec q.vec := rfl

variable [LinearOrderedField 𝔽] (p : LinearSystem 𝔽 n)

/-- The set of solutions of the linear system. -/
@[simp low] def solutions : Set (Fin n → 𝔽) := { x | p.mat *ᵥ x ≤ p.vec }

/-- Two linear systems are said to be equivalent when their sets of solutions are equal. -/
instance : HasEquiv (LinearSystem 𝔽 n) := ⟨(·.solutions = ·.solutions)⟩

instance isSetoid (𝔽 n) [LinearOrderedField 𝔽] : Setoid (LinearSystem 𝔽 n) :=
  ⟨instHasEquiv.Equiv, fun _ ↦ rfl, Eq.symm, Eq.trans⟩

@[simp] theorem equiv_def : p ≈ q ↔ p.solutions = q.solutions := Iff.rfl

@[simp] lemma mem_solutions : x ∈ p.solutions ↔ p.mat *ᵥ x ≤ p.vec := Set.mem_setOf

@[simp] lemma mem_solutions_of {x : Fin n → 𝔽} : x ∈ (of A b).solutions ↔ A *ᵥ x ≤ b := Set.mem_setOf

@[simp] theorem empty_solutions : (empty : LinearSystem 𝔽 n).solutions = Set.univ := by simp

@[simp] lemma vecCons_mulVec
  {m n : ℕ} (y : Fin n → 𝔽) (A : Matrix (Fin m) (Fin n) 𝔽) (x : Fin n → 𝔽)
  : vecCons y A *ᵥ x = vecCons (y ⬝ᵥ x) (A *ᵥ x) := by
  funext x
  cases x using Fin.cases <;> rfl

@[simp] lemma vecCons_le_vecCons {n : ℕ} (a b : 𝔽) (x y : Fin n → 𝔽)
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

@[simp] theorem cons_solutions
  : (cons y b p : LinearSystem 𝔽 n).solutions = {x | y ⬝ᵥ x ≤ b ∧ p.mat *ᵥ x ≤ p.vec} := by simp

/-- The set of solutions of the concatenation of two linear systems is the intersection of their
  sets of solutions. -/
@[simp low] theorem concat_solutions : (p ++ q).solutions = p.solutions ∩ q.solutions := by
  simp_rw [Set.ext_iff, Set.mem_inter_iff]
  intro x
  constructor <;> intro h
  . simp_rw [mem_solutions, concat_mat, concat_vec, Pi.le_def] at h
    constructor <;> (rw [mem_solutions, Pi.le_def]; intro i)
    . have := h (i.castAdd q.m)
      simp_all [mulVec]
    . have := h (i.natAdd p.m)
      simp_all [mulVec]
  . simp_rw [mem_solutions, concat_m, concat_mat, concat_vec, Pi.le_def]
    intro i
    cases i using Fin.addCases
    <;> simp only [mulVec, Fin.append_left, Fin.append_right]
    . apply h.1
    . apply h.2

@[simp] theorem mem_concat : x ∈ (p ++ q).solutions ↔ x ∈ p.solutions ∧ x ∈ q.solutions := by
  rw [←Set.mem_inter_iff, concat_solutions]

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

/-- A system defined by a single equation `aᵀ x ≤ b`. -/
def semiSpace (a : Fin n → 𝔽) (b : 𝔽) : LinearSystem 𝔽 n := of ![a] ![b]

section
omit [LinearOrderedField 𝔽]

theorem semiSpace_m {a : Fin n → 𝔽} {b : 𝔽} : (semiSpace a b).m = 1 :=
  rfl
theorem semiSpace_mat {a : Fin n → 𝔽} {b : 𝔽} : (semiSpace a b).mat = ![a] := rfl
theorem semiSpace_vec {a : Fin n → 𝔽} {b : 𝔽} : (semiSpace a b).vec = ![b] := rfl

end

@[simp low] theorem semiSpace_solutions : (semiSpace a b).solutions = { x : Fin n → 𝔽 | a ⬝ᵥ x ≤ b } := by
  simp [semiSpace]

@[simp] theorem mem_semiSpace : ∀ x : Fin n → 𝔽, x ∈ (semiSpace a b).solutions ↔ a ⬝ᵥ x ≤ b := by
  simp [semiSpace]

abbrev ith_semiSpace (S : LinearSystem 𝔽 n) (i : Fin S.m) : LinearSystem 𝔽 n :=
  semiSpace (S.mat i) (S.vec i)
