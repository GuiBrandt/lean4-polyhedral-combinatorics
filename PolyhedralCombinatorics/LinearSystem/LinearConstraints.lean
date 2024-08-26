import PolyhedralCombinatorics.LinearSystem.Basic

inductive LinearConstraint.Comparator | le | eq | ge

variable
  (𝔽 : Type*) [LinearOrderedField 𝔽] -- Field type
  (n : ℕ) -- Dimension of the space

/-- `LinearConstraint n` is the type of linear constraints on `n` variables. -/
structure LinearConstraint where
  coefficients : Fin n → 𝔽
  comparator : LinearConstraint.Comparator
  rhs : 𝔽

variable {𝔽 n}

namespace LinearConstraint
open Matrix

/-- Converts a linear constraint into a list o extended matrix rows for a
  linear system. -/
def toExtendedRows : LinearConstraint 𝔽 n → List ((Fin n → 𝔽) × 𝔽)
| ⟨y, .le, b⟩ => [(y, b)]
| ⟨y, .eq, b⟩ => [(y, b), (-y, -b)]
| ⟨y, .ge, b⟩ => [(-y, -b)]

@[simp] lemma le_toExtendedRows : @toExtendedRows 𝔽 _ n ⟨y, .le, b⟩ = [(y, b)] := rfl
@[simp] lemma eq_toExtendedRows : @toExtendedRows 𝔽 _ n ⟨y, .eq, b⟩ = [(y, b), (-y, -b)] := rfl
@[simp] lemma ge_toExtendedRows : @toExtendedRows 𝔽 _ n ⟨y, .ge, b⟩ = [(-y, -b)] := rfl

/-- Whether a linear constraint is valid for a given vector. -/
def valid : LinearConstraint 𝔽 n → (Fin n → 𝔽) → Prop
| ⟨y, cmp, b⟩, x =>
  let p := y ⬝ᵥ x
  match cmp with | .le => p ≤ b | .eq => p = b | .ge => p ≥ b

@[simp] lemma le_valid : @valid 𝔽 _ n ⟨y, Comparator.le, b⟩ x = (y ⬝ᵥ x ≤ b) := rfl
@[simp] lemma eq_valid : @valid 𝔽 _ n ⟨y, Comparator.eq, b⟩ x = (y ⬝ᵥ x = b) := rfl
@[simp] lemma ge_valid : @valid 𝔽 _ n ⟨y, Comparator.ge, b⟩ x = (y ⬝ᵥ x ≥ b) := rfl

end LinearConstraint

namespace LinearSystem

open LinearConstraint

/-- Constructs a polyhedron description from a list of linear constraints. -/
def ofConstraints (constraints : List (LinearConstraint 𝔽 n)) : LinearSystem 𝔽 n :=
  let rows := constraints.bind LinearConstraint.toExtendedRows
  ⟨rows.length, Matrix.of (Prod.fst ∘ rows.get), Prod.snd ∘ rows.get⟩

section toSet_ofConstraints
open LinearConstraint

-- FIXME: there must be a better way?
private lemma prod_eq (p : α × β) : p.1 = a ∧ p.2 = b ↔ p = (a, b) := by
  obtain ⟨fst, snd⟩ := p
  simp_all only [Prod.mk.injEq]

private lemma le_lemma
  {constraints : List (LinearConstraint 𝔽 n)} {y : Fin n → 𝔽} {b : 𝔽}
  : ⟨y, Comparator.le, b⟩ ∈ constraints →
    ∃ i, (LinearSystem.ofConstraints constraints).mat i = y ∧ (LinearSystem.ofConstraints constraints).vec i = b := by
  let rows := constraints.bind toExtendedRows
  intro h
  show ∃ i : Fin rows.length, rows[i].1 = y ∧ rows[i].2 = b
  simp_rw [prod_eq]
  apply List.mem_iff_get.mp
  rw [List.mem_bind]
  exact ⟨_, h, by simp [toExtendedRows]⟩

private lemma ge_lemma
  {constraints : List (LinearConstraint 𝔽 n)} {y : Fin n → 𝔽} {b : 𝔽}
  : ⟨y, Comparator.ge, b⟩ ∈ constraints →
    ∃ i, (LinearSystem.ofConstraints constraints).mat i = -y ∧ (LinearSystem.ofConstraints constraints).vec i = -b := by
  let rows := constraints.bind toExtendedRows
  intro h
  show ∃ i : Fin rows.length, rows[i].1 = -y ∧ rows[i].2 = -b
  simp_rw [prod_eq]
  apply List.mem_iff_get.mp
  rw [List.mem_bind]
  exact ⟨_, h, by simp [toExtendedRows]⟩

private lemma eq_lemma
  {constraints : List (LinearConstraint 𝔽 n)} {y : Fin n → 𝔽} {b : 𝔽}
  : ⟨y, Comparator.eq, b⟩ ∈ constraints →
      (∃ i, (LinearSystem.ofConstraints constraints).mat i = y ∧ (LinearSystem.ofConstraints constraints).vec i = b)
    ∧ (∃ i, (LinearSystem.ofConstraints constraints).mat i = -y ∧ (LinearSystem.ofConstraints constraints).vec i = -b) := by
  let rows := constraints.bind toExtendedRows
  intro h
  show  (∃ i : Fin rows.length, rows[i].1 = y ∧ rows[i].2 = b)
      ∧ (∃ i : Fin rows.length, rows[i].1 = -y ∧ rows[i].2 = -b)
  simp_rw [prod_eq]
  constructor <;> (
    apply List.mem_iff_get.mp
    rw [List.mem_bind]
    exact ⟨_, h, by simp [toExtendedRows]⟩
  )

theorem toSet_ofConstraints
  : (ofConstraints constraints).toSet = { x : Fin n → 𝔽 | ∀ c ∈ constraints, c.valid x } := by
  let rows := constraints.bind toExtendedRows
  simp_rw [Set.ext_iff, ofConstraints, toSet, Set.mem_setOf]
  intro x
  conv =>
    congr
    . rw [Pi.le_def]
      intro i
      change (rows.get i).1 ⬝ᵥ x ≤ (rows.get i).2
      rfl
    . rfl
  sorry

end toSet_ofConstraints

end LinearSystem
