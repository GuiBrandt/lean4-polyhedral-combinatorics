import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

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
-/

variable
  (𝔽 : Type*) [LinearOrderedField 𝔽] -- Field type
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

variable {𝔽 m n} (p q : LinearSystem 𝔽 n)

/-- Constructs a linear system defined by a `m × n` coefficient matrix `A` and an `m × 1` column
  vector `b`. -/
abbrev of (A : Matrix (Fin m) (Fin n) 𝔽) (b : Fin m → 𝔽) : LinearSystem 𝔽 n := ⟨m, A, b⟩

/-- The concatenation of two linear systems. -/
def concat : LinearSystem 𝔽 n :=
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

/-- The set of solutions of the linear system. -/
@[simp] def solutions : Set (Fin n → 𝔽) := { x | p.mat *ᵥ x ≤ p.vec }

/-- Two linear systems are said to be equivalent when their sets of solutions are equal. -/
instance : HasEquiv (LinearSystem 𝔽 n) := ⟨(·.solutions = ·.solutions)⟩

instance isSetoid (𝔽 n) [LinearOrderedField 𝔽] : Setoid (LinearSystem 𝔽 n) :=
  ⟨instHasEquiv.Equiv, fun _ ↦ rfl, Eq.symm, Eq.trans⟩
