import PolyhedralCombinatorics.Polyhedron.Defs

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ} (p : Polyhedron 𝔽 n)

@[simp] theorem toSet_ofLinearSystem {d : LinearSystem 𝔽 n} : (ofLinearSystem d).toSet = d.toSet := rfl

@[simp] theorem empty_toSet : (∅ : Polyhedron 𝔽 n).toSet = ∅ := by
  change empty.toSet = ∅
  rw [empty, toSet_ofLinearSystem, Set.eq_empty_iff_forall_not_mem]
  intro x h
  have := calc
    1 ≤ -((fun _ ↦ 1) ⬝ᵥ x) := le_neg.mpr $ h 0
    _ = (fun _ ↦ -1) ⬝ᵥ x := by simp [dotProduct]
    _ ≤ 0 := h 1
  linarith

theorem mem_def : x ∈ p ↔ x ∈ p.toSet := Iff.rfl

/-- The empty polyhedron has no points. -/
theorem not_mem_empty : ∀ x, x ∉ (∅ : Polyhedron 𝔽 n) := by simp [mem_def]

@[simp] theorem univ_toSet : (⊤ : Polyhedron 𝔽 n).toSet = Set.univ := by
  show univ.toSet = Set.univ
  simp [univ]

/-- The empty polyhedron contains all points. -/
theorem mem_univ : ∀ x, x ∈ (⊤ : Polyhedron 𝔽 n) := by simp [mem_def]

theorem toSet_inj {p q : Polyhedron 𝔽 n} : p.toSet = q.toSet ↔ p = q := by
  constructor <;> intro h
  . induction p, q using Quotient.ind₂
    rename_i p q
    rw [Quotient.eq]
    show p.toSet = q.toSet
    simp_all only [toSet, Quotient.lift_mk]
  . subst h
    rfl

@[simp] theorem ofDescr_eq_ofDescr {d d'  : LinearSystem 𝔽 n}
  : ofLinearSystem d = ofLinearSystem d' ↔ d.toSet = d'.toSet := by
  simp_rw [←toSet_inj, ofLinearSystem, toSet, Quotient.lift_mk]

/-- The set of points of a polyhedron is convex. -/
theorem toSet_convex : Convex 𝔽 p.toSet :=
  Quot.recOn p
    (fun P ↦ by
      intro
        x x_mem_P
        y y_mem_P
        α β α_nonneg β_nonneg αβ_affine
      show P.mat *ᵥ (α • x + β • y) ≤ P.vec
      calc
        P.mat *ᵥ (α • x + β • y) = α • P.mat *ᵥ x + β • P.mat *ᵥ y := by
          simp_rw [mulVec_add, mulVec_smul]
        _ ≤ α • P.vec + β • P.vec :=
          add_le_add
            (smul_le_smul_of_nonneg_left x_mem_P α_nonneg)
            (smul_le_smul_of_nonneg_left y_mem_P β_nonneg)
        _ = P.vec := by rw [←add_smul, αβ_affine, one_smul])
    (fun _ _ ↦ by simp)

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

@[simp] theorem mem_ofConstraints (constraints : List (LinearConstraint 𝔽 n))
  : ∀ x, x ∈ ofLinearSystem (ofConstraints constraints) ↔ ∀ c ∈ constraints, c.valid x := by
  intro x
  let rows := constraints.bind toExtendedRows
  constructor <;> intro h
  . show ∀ constr ∈ constraints, constr.valid _
    intro ⟨y, cmp, b⟩ mem_constraints
    cases cmp <;> simp only [valid]
    case le =>
      have ⟨i, hy, hb⟩ := le_lemma mem_constraints
      subst hy hb
      apply h
    case ge =>
      have ⟨i, hy, hb⟩ := ge_lemma mem_constraints
      rw [←neg_eq_iff_eq_neg] at hy hb
      subst hy hb
      rw [neg_dotProduct, ge_iff_le, neg_le_neg_iff]
      apply h
    case eq =>
      have ⟨⟨i₁, hy₁, hb₁⟩, ⟨i₂, hy₂, hb₂⟩⟩ := eq_lemma mem_constraints
      apply le_antisymm
      . subst hy₁ hb₁
        apply h
      . rw [←neg_eq_iff_eq_neg] at hy₂ hb₂
        subst hy₂ hb₂
        rw [neg_dotProduct, neg_le_neg_iff]
        apply h
  . show ∀ (i : Fin rows.length), rows[i].1 ⬝ᵥ _ ≤ rows[i].2
    intro i
    show rows[i].1 ⬝ᵥ _ ≤ rows[i].2
    have : rows[i] ∈ rows := by apply List.get_mem
    have ⟨⟨y, cmp, b⟩, mem_constraints, h'⟩ := List.mem_bind.mp this
    have := h _ mem_constraints
    cases cmp <;> (
      simp_all only [toExtendedRows, valid, List.mem_singleton, List.mem_pair]
      try cases h'
      all_goals simp_all only [neg_dotProduct, neg_le_neg_iff, le_refl]
    )

/-- The set of points of a polyhedron defined by a given list of `constraints` is the set of
  points that satisfy those constraints. -/
@[simp] theorem toSet_ofConstraints (constraints : List (LinearConstraint 𝔽 n))
  : (ofConstraints constraints).toSet = { x | ∀ constr ∈ constraints, constr.valid x } :=
  Set.ext_iff.mpr (mem_ofConstraints _)

end toSet_ofConstraints

instance : Inter (Polyhedron 𝔽 n) where
  inter := Quotient.lift₂ (ofLinearSystem $ concat · ·) $ by
    intro a b a' b' ha hb
    simp_rw [ofDescr_eq_ofDescr, toSet_concat]
    change a.toSet = a'.toSet at ha
    change b.toSet = b'.toSet at hb
    simp_all only

@[simp] theorem toSet_inter (p q : Polyhedron 𝔽 n) : (p ∩ q).toSet = p.toSet ∩ q.toSet :=
  Quotient.inductionOn₂ p q LinearSystem.toSet_concat

@[simp] theorem mem_inter {p q : Polyhedron 𝔽 n} {x : Fin n → 𝔽} : x ∈ p ∩ q ↔ x ∈ p ∧ x ∈ q := by
  induction p, q using Quotient.ind₂
  simp only [mem_def, toSet_inter, Set.mem_inter_iff]

instance : HasSubset (Polyhedron 𝔽 n) := ⟨(·.toSet ⊆ ·.toSet)⟩

theorem subset_iff {p q : Polyhedron 𝔽 n} : p ⊆ q ↔ ∀ x, x ∈ p → x ∈ q := by
  constructor <;> intro h <;> exact h

theorem empty_subset (p : Polyhedron 𝔽 n) : ∅ ⊆ p := by simp [subset_iff, not_mem_empty]

theorem subset_univ (p : Polyhedron 𝔽 n) : p ⊆ ⊤ := by simp [subset_iff, mem_univ]

instance : SemilatticeInf (Polyhedron 𝔽 n) where
  inf := (· ∩ ·)
  le := (· ⊆ ·)
  le_refl p := subset_refl p.toSet
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h h' := toSet_inj.mp $ subset_antisymm h h'
  inf_le_left _ _ _ h := And.left $ mem_inter.mp h
  inf_le_right _ _ _ h := And.right $ mem_inter.mp h
  le_inf _ _ _ h h' _ hx := mem_inter.mpr $ And.intro (h hx) (h' hx)
