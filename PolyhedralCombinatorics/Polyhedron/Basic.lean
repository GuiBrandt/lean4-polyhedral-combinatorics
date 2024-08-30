import PolyhedralCombinatorics.LinearSystem.LinearConstraints

import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.Normed.Group.Constructions -- Vector (Pi type) norm

/-!
# Polyhedra

This defines basic properties of polyhedra.

Polyhedra in `n` dimensions over a linear ordered field `𝔽` are represented
with `Polhedron 𝔽 n`.

## Main definitions

* `Polyhedron`: The type of polyhedra.
* `Polyhedron.ofLinearSystem`: The polyhedron defined by a linear system.

## Main results
* `Polyhedron.toSet_convex`: The set of points of a polyhedron is convex.
-/

/-- `Polyhedron 𝔽 n` is the type of polyhedra in `𝔽^n`, where `𝔽` is a linear ordered field. -/
def Polyhedron (𝔽 : Type u₁) [LinearOrderedField 𝔽] (n : ℕ) := Quotient (LinearSystem.isSetoid 𝔽 n)

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n} (p q r : Polyhedron 𝔽 n)

/-- Notation for the polyhedron `{ x ∈ 𝔽^n | A x ≤ b }` -/
@[coe] def ofLinearSystem : LinearSystem 𝔽 n → Polyhedron 𝔽 n := Quotient.mk _

instance : Coe (LinearSystem 𝔽 n) (Polyhedron 𝔽 n) := ⟨ofLinearSystem⟩

/-- The set of points in `p`. -/
@[coe] def toSet : Set (Fin n → 𝔽) := Quotient.lift solutions (fun _ _ ↦ id) p

instance instCoeSet : Coe (Polyhedron 𝔽 n) (Set (Fin n → 𝔽)) := ⟨toSet⟩

@[simp] theorem toSet_ofLinearSystem {d : LinearSystem 𝔽 n} : (ofLinearSystem d).toSet = d.solutions := rfl

theorem toSet_inj {p q : Polyhedron 𝔽 n} : p.toSet = q.toSet ↔ p = q := by
  constructor <;> intro h
  . induction p, q using Quotient.ind₂
    rename_i p q
    rw [Quotient.eq]
    show p.solutions = q.solutions
    simp_all only [toSet, Quotient.lift_mk]
  . subst h
    rfl

/-- Membership in a polyhedron. -/
abbrev Mem (x : Fin n → 𝔽) (p : Polyhedron 𝔽 n) := x ∈ p.toSet

instance instMembership : Membership (Fin n → 𝔽) (Polyhedron 𝔽 n) := ⟨Mem⟩

theorem mem_def : x ∈ p ↔ x ∈ p.toSet := Iff.rfl

@[ext] theorem ext {p q : Polyhedron 𝔽 n} : (∀ x, x ∈ p ↔ x ∈ q) → p = q := toSet_inj.mp ∘ Set.ext

@[simp] theorem mem_ofLinearSystem {d : LinearSystem 𝔽 n}
  : x ∈ ofLinearSystem d ↔ x ∈ d.solutions := by
  simp_rw [mem_def, ofLinearSystem, toSet, Quotient.lift_mk]

@[simp] theorem mem_ofLinearSystem_of {m} {A : Matrix (Fin m) (Fin n) 𝔽} {b : Fin m → 𝔽}
  : x ∈ ofLinearSystem (of A b) ↔ A *ᵥ x ≤ b := by
  simp_rw [mem_ofLinearSystem, mem_solutions]

/-- A polyhedron `P` is a polytope when it is limited, i.e. every point `x ∈ P`
  satisfies `‖x‖ ≤ α` for some `α`. -/
def IsPolytope [Norm (Fin n → 𝔽)] := ∃ α, ∀ x ∈ p, ‖x‖ ≤ α

example : Polyhedron 𝔽 2 :=
  let A : Matrix (Fin 4) (Fin 2) 𝔽 :=
    !![ 1, -1;
       -1, -1;
        1,  0;
        0,  1]
  let b : Fin 4 → 𝔽 := ![-2, -2, 4, 4]
  of A b

/-- The empty polyhedron (`∅`). -/
def empty : Polyhedron 𝔽 n := of (0 : Matrix (Fin 1) (Fin n) 𝔽) ![-1]

instance : EmptyCollection (Polyhedron 𝔽 n) := ⟨empty⟩

instance : Bot (Polyhedron 𝔽 n) := ⟨empty⟩

/-- The universe polyhedron (`𝔽^n`). -/
def univ : Polyhedron 𝔽 n := ofLinearSystem $ of 0 ![]
instance : Top (Polyhedron 𝔽 n) := ⟨univ⟩

@[simp] theorem empty_toSet : (∅ : Polyhedron 𝔽 n).toSet = ∅ := by
  change empty.toSet = ∅
  simp [empty, Set.eq_empty_iff_forall_not_mem, Pi.le_def]

/-- The empty polyhedron has no points. -/
theorem not_mem_empty : ∀ x, x ∉ (∅ : Polyhedron 𝔽 n) := by simp [mem_def]

theorem eq_empty_iff : p = ∅ ↔ ∀ x, x ∉ p := by
  constructor <;> intro h
  . subst h
    apply not_mem_empty
  . ext x
    simp_rw [h, not_mem_empty]

@[simp] theorem univ_toSet : (⊤ : Polyhedron 𝔽 n).toSet = Set.univ := by
  show univ.toSet = Set.univ
  simp [univ]

/-- The empty polyhedron contains all points. -/
theorem mem_univ : ∀ x, x ∈ (⊤ : Polyhedron 𝔽 n) := by simp [mem_def]

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

@[simp] theorem toSet_inter : (p ∩ q).toSet = p.toSet ∩ q.toSet :=
  Quotient.inductionOn₂ p q solutions_concat

@[simp] theorem mem_inter {p q : Polyhedron 𝔽 n} {x : Fin n → 𝔽} : x ∈ p ∩ q ↔ x ∈ p ∧ x ∈ q := by
  induction p, q using Quotient.ind₂
  simp only [mem_def, toSet_inter, Set.mem_inter_iff]

abbrev Subset (p q : Polyhedron 𝔽 n) : Prop := ∀ ⦃x⦄, x ∈ p → x ∈ q

def Subset.refl : Subset p p := subset_refl p.toSet

def Subset.rfl {p : Polyhedron 𝔽 n} : Subset p p := refl p

def Subset.trans (p q r: Polyhedron 𝔽 n) : Subset p q → Subset q r → Subset p r :=
  Set.Subset.trans

def Subset.antisymm (pq : Subset p q) (qp : Subset q p) : p = q :=
  toSet_inj.mp $ subset_antisymm pq qp

instance : HasSubset (Polyhedron 𝔽 n) := ⟨Subset⟩

theorem subset_iff : p ⊆ q ↔ ∀ x, x ∈ p → x ∈ q := Iff.rfl

theorem empty_subset : ∅ ⊆ p := by simp [subset_iff, not_mem_empty]

theorem subset_univ : p ⊆ ⊤ := by simp [subset_iff, mem_univ]

theorem inter_subset_left : p ∩ q ⊆ p := fun _ h ↦ And.left $ mem_inter.mp h

theorem inter_subset_right : p ∩ q ⊆ q := fun _ h ↦ And.right $ mem_inter.mp h

theorem subset_inter (pq : p ⊆ q) (qr : p ⊆ r) : p ⊆ q ∩ r :=
  fun _ hx ↦ mem_inter.mpr $ And.intro (pq hx) (qr hx)

instance : IsPartialOrder (Polyhedron 𝔽 n) (· ⊆ ·) where
  refl := Subset.refl
  trans := Subset.trans
  antisymm := Subset.antisymm

instance : SemilatticeInf (Polyhedron 𝔽 n) where
  inf := (· ∩ ·)
  le := (· ⊆ ·)
  le_refl := Subset.refl
  le_trans := Subset.trans
  le_antisymm := Subset.antisymm
  inf_le_left := inter_subset_left
  inf_le_right := inter_subset_right
  le_inf := subset_inter
