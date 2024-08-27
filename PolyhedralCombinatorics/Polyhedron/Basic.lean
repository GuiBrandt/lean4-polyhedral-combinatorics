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

@[simp] theorem ofLinearSystem_eq_ofLinearSystem {d d'  : LinearSystem 𝔽 n}
  : ofLinearSystem d = ofLinearSystem d' ↔ d.toSet = d'.toSet := by
  simp_rw [←toSet_inj, ofLinearSystem, toSet, Quotient.lift_mk]

/-- The set of points of a polyhedron is convex. -/
theorem toSet_convex : Convex 𝔽 p.toSet :=
  Quot.recOn p
    (fun p x x_mem_P y y_mem_P α β α_nonneg β_nonneg αβ_affine ↦ by
      calc
        p.mat *ᵥ (α • x + β • y) = α • p.mat *ᵥ x + β • p.mat *ᵥ y := by
          simp_rw [mulVec_add, mulVec_smul]
        _ ≤ α • p.vec + β • p.vec :=
          add_le_add
            (smul_le_smul_of_nonneg_left x_mem_P α_nonneg)
            (smul_le_smul_of_nonneg_left y_mem_P β_nonneg)
        _ = p.vec := by rw [←add_smul, αβ_affine, one_smul])
    (fun _ _ _ ↦ rfl)

@[simp] theorem mem_ofConstraints {constraints : List (LinearConstraint 𝔽 n)}
  : ∀ x, x ∈ ofLinearSystem (ofConstraints constraints) ↔ ∀ c ∈ constraints, c.valid x :=
  LinearSystem.mem_toSet_ofConstraints

/-- The set of points of a polyhedron defined by a given list of `constraints` is the set of
  points that satisfy those constraints. -/
@[simp] theorem toSet_ofConstraints {constraints : List (LinearConstraint 𝔽 n)}
  : (ofConstraints constraints).toSet = { x | ∀ constr ∈ constraints, constr.valid x } :=
  LinearSystem.toSet_ofConstraints

/-- Intersection of polyhedra. -/
def inter : Polyhedron 𝔽 n → Polyhedron 𝔽 n → Polyhedron 𝔽 n :=
  Quotient.lift₂ (ofLinearSystem $ concat · ·) $ by
    intro a b a' b' ha hb
    simp_rw [ofLinearSystem_eq_ofLinearSystem, toSet_concat]
    change a.toSet = a'.toSet at ha
    change b.toSet = b'.toSet at hb
    simp_all only

instance : Inter (Polyhedron 𝔽 n) := ⟨inter⟩

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
