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

variable {𝔽 n} {y : Fin n → 𝔽} {b : 𝔽}

namespace LinearConstraint
open Matrix

/-- Converts a linear constraint into a list o extended matrix rows for a
  linear system. -/
def toExtendedRows : LinearConstraint 𝔽 n → List ((Fin n → 𝔽) × 𝔽)
| ⟨y, .le, b⟩ => [(y, b)]
| ⟨y, .eq, b⟩ => [(y, b), (-y, -b)]
| ⟨y, .ge, b⟩ => [(-y, -b)]

@[simp] lemma le_toExtendedRows : toExtendedRows ⟨y, .le, b⟩ = [(y, b)] := rfl
@[simp] lemma eq_toExtendedRows : toExtendedRows ⟨y, .eq, b⟩ = [(y, b), (-y, -b)] := rfl
@[simp] lemma ge_toExtendedRows : toExtendedRows ⟨y, .ge, b⟩ = [(-y, -b)] := rfl

/-- Whether a linear constraint is valid for a given vector. -/
def valid : LinearConstraint 𝔽 n → (Fin n → 𝔽) → Prop
| ⟨y, cmp, b⟩, x =>
  let p := y ⬝ᵥ x
  match cmp with | .le => p ≤ b | .eq => p = b | .ge => p ≥ b

@[simp] lemma le_valid : valid ⟨y, Comparator.le, b⟩ x = (y ⬝ᵥ x ≤ b) := rfl
@[simp] lemma eq_valid : valid ⟨y, Comparator.eq, b⟩ x = (y ⬝ᵥ x = b) := rfl
@[simp] lemma ge_valid : valid ⟨y, Comparator.ge, b⟩ x = (y ⬝ᵥ x ≥ b) := rfl

lemma eq_valid_iff
  : valid ⟨y, Comparator.eq, b⟩ x
    ↔ valid ⟨y, Comparator.le, b⟩ x ∧ valid ⟨y, Comparator.ge, b⟩ x := by simp [le_antisymm_iff]

end LinearConstraint

namespace LinearSystem

open LinearConstraint

/-- Constructs a polyhedron description from a list of linear constraints. -/
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

macro "constraint_lemma_tac" h:ident : tactic =>
  `(tactic|
    simp_rw [ofConstraints_apply_eq_lemma]
    <;> exact List.mem_iff_get.mp $ List.mem_bind.mpr ⟨_, $h, by simp [toExtendedRows]⟩)

private lemma le_lemma (h : ⟨y, Comparator.le, b⟩ ∈ cs)
  : let s := ofConstraints cs; ∃ i, s.mat i = y ∧ s.vec i = b := by
  constraint_lemma_tac h

private lemma ge_lemma (h : ⟨y, Comparator.ge, b⟩ ∈ cs)
  : let s := ofConstraints cs; ∃ i, -(s.mat i) = y ∧ -(s.vec i) = b := by
  simp_rw [neg_eq_iff_eq_neg]
  constraint_lemma_tac h

private lemma eq_lemma (h : ⟨y, Comparator.eq, b⟩ ∈ cs)
  : let s := ofConstraints cs;
    (∃ i, s.mat i = y ∧ s.vec i = b) ∧ (∃ i, -(s.mat i) = y ∧ -(s.vec i) = b) := by
  simp_rw [neg_eq_iff_eq_neg]
  constructor <;> constraint_lemma_tac h

theorem mem_toSet_ofConstraints (x : Fin n → 𝔽)
  : x ∈ (ofConstraints cs).toSet ↔ ∀ c ∈ cs, c.valid x := by
  let rows := cs.bind toExtendedRows
  constructor
  . show x ∈ (ofConstraints cs).toSet → ∀ c ∈ cs, c.valid _
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
      simp_rw [valid, neg_dotProduct, neg_le_neg_iff]
      apply h
  . show (∀ c ∈ cs, c.valid x) → ∀ (i : Fin rows.length), rows[i].1 ⬝ᵥ _ ≤ rows[i].2
    intro h i
    have : rows[i] ∈ rows := by apply List.get_mem
    have ⟨⟨y, cmp, b⟩, mem_cs, h'⟩ := List.mem_bind.mp this
    have := h _ mem_cs
    cases cmp <;> (
      simp_all only [toExtendedRows, valid, List.mem_singleton, List.mem_pair]
      try cases h'
      all_goals simp_all only [neg_dotProduct, neg_le_neg_iff, le_refl]
    )

theorem toSet_ofConstraints
  : (ofConstraints cs).toSet = { x : Fin n → 𝔽 | ∀ c ∈ cs, c.valid x } :=
  Set.ext_iff.mpr mem_toSet_ofConstraints

end toSet_ofConstraints

end LinearSystem
