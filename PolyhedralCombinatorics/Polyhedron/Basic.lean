import PolyhedralCombinatorics.Polyhedron.Defs

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ} (p q r : Polyhedron 𝔽 n)

@[simp] theorem toSet_ofLinearSystem {d : LinearSystem 𝔽 n} : (ofLinearSystem d).toSet = d.solutions := rfl

@[simp] theorem empty_toSet : (∅ : Polyhedron 𝔽 n).toSet = ∅ := by
  change empty.toSet = ∅
  simp [empty, Set.eq_empty_iff_forall_not_mem, Pi.le_def]

theorem mem_def : x ∈ p ↔ x ∈ p.toSet := Iff.rfl

@[simp] theorem mem_ofLinearSystem {d : LinearSystem 𝔽 n}
  : x ∈ ofLinearSystem d ↔ x ∈ d.solutions := by
  simp_rw [mem_def, ofLinearSystem, toSet, Quotient.lift_mk]

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
    show p.solutions = q.solutions
    simp_all only [toSet, Quotient.lift_mk]
  . subst h
    rfl

@[simp] theorem ofLinearSystem_eq_ofLinearSystem {d d'  : LinearSystem 𝔽 n}
  : ofLinearSystem d = ofLinearSystem d' ↔ d.solutions = d'.solutions := by
  simp_rw [←toSet_inj, ofLinearSystem, toSet, Quotient.lift_mk]

/-- The set of points of a polyhedron is convex. -/
theorem toSet_convex : Convex 𝔽 p.toSet := Quotient.recOn p solutions_convex (fun _ _ _ ↦ rfl)

@[simp] theorem mem_ofConstraints {constraints : List (LinearConstraint 𝔽 n)}
  : ∀ x, x ∈ ofLinearSystem (ofConstraints constraints) ↔ ∀ c ∈ constraints, c.valid x :=
  mem_solutions_ofConstraints

/-- The set of points of a polyhedron defined by a given list of `constraints` is the set of
  points that satisfy those constraints. -/
@[simp] theorem toSet_ofConstraints {constraints : List (LinearConstraint 𝔽 n)}
  : (ofLinearSystem (ofConstraints constraints)).toSet = { x | ∀ constr ∈ constraints, constr.valid x } :=
  solutions_ofConstraints

/-- Intersection of polyhedra. -/
def inter : Polyhedron 𝔽 n → Polyhedron 𝔽 n → Polyhedron 𝔽 n :=
  Quotient.lift₂ (ofLinearSystem $ concat · ·) $ by
    intro a b a' b' ha hb
    simp_rw [ofLinearSystem_eq_ofLinearSystem, solutions_concat]
    change a.solutions = a'.solutions at ha
    change b.solutions = b'.solutions at hb
    simp_all only

instance : Inter (Polyhedron 𝔽 n) := ⟨inter⟩

theorem ext_iff {p q : Polyhedron 𝔽 n} : p = q ↔ (∀ x, x ∈ p ↔ x ∈ q) := by
  rw [←toSet_inj]
  exact Set.ext_iff

@[simp] theorem toSet_inter : (p ∩ q).toSet = p.toSet ∩ q.toSet :=
  Quotient.inductionOn₂ p q solutions_concat

@[simp] theorem mem_inter {p q : Polyhedron 𝔽 n} {x : Fin n → 𝔽} : x ∈ p ∩ q ↔ x ∈ p ∧ x ∈ q := by
  induction p, q using Quotient.ind₂
  simp only [mem_def, toSet_inter, Set.mem_inter_iff]

abbrev Subset : Polyhedron 𝔽 n → Polyhedron 𝔽 n → Prop := (·.toSet ⊆ ·.toSet)

def Subset.refl : Subset p p := subset_refl p.toSet

def Subset.rfl {p : Polyhedron 𝔽 n} : Subset p p := refl p

@[trans] def Subset.trans : Subset p q → Subset q r → Subset p r :=
  Set.Subset.trans

@[trans] def Subset.antisymm (pq : Subset p q) (qp : Subset q p) : p = q :=
  toSet_inj.mp $ subset_antisymm pq qp

instance : HasSubset (Polyhedron 𝔽 n) := ⟨Subset⟩

theorem subset_iff : p ⊆ q ↔ ∀ x, x ∈ p → x ∈ q := Iff.rfl

theorem empty_subset : ∅ ⊆ p := by simp [subset_iff, not_mem_empty]

theorem subset_univ : p ⊆ ⊤ := by simp [subset_iff, mem_univ]

theorem inter_subset_left : p ∩ q ⊆ p := fun _ h ↦ And.left $ mem_inter.mp h

theorem inter_subset_right : p ∩ q ⊆ q := fun _ h ↦ And.right $ mem_inter.mp h

theorem subset_inter (pq : p ⊆ q) (qr : p ⊆ r) : p ⊆ q ∩ r :=
  fun _ hx ↦ mem_inter.mpr $ And.intro (pq hx) (qr hx)

instance : SemilatticeInf (Polyhedron 𝔽 n) where
  inf := (· ∩ ·)
  le := (· ⊆ ·)
  le_refl := Subset.refl
  le_trans := Subset.trans
  le_antisymm := Subset.antisymm
  inf_le_left := inter_subset_left
  inf_le_right := inter_subset_right
  le_inf := subset_inter
