import Mathlib.Data.Real.Basic
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Notation

import Mathlib.Analysis.Convex.Basic

-- Vector (Pi type) norm
import Mathlib.Analysis.Normed.Group.Constructions

structure PolyhedronDescr (S : Type*) (n : ℕ) where
  m : ℕ
  mat : Matrix (Fin m) (Fin n) S
  vec : Fin m → S

namespace PolyhedronDescr
open Matrix

variable {S} [LinearOrderedField S] {n : ℕ} (p q : PolyhedronDescr S n) (x : Fin n → S)

@[simp] def toSet : Set (Fin n → S) := { x | p.mat *ᵥ x ≤ p.vec }

instance : Inter (PolyhedronDescr S n) where
  inter p q :=
    {
      m := p.m + q.m,
      mat := Matrix.of fun i j =>
        if h : i < p.m then
          p.mat ⟨i, h⟩ j
        else
          q.mat ⟨i - p.m, Nat.sub_lt_left_of_lt_add (not_lt.mp h) i.prop⟩ j
      vec := fun i =>
        if h : i < p.m then
          p.vec ⟨i, h⟩
        else
          q.vec ⟨i - p.m, Nat.sub_lt_left_of_lt_add (not_lt.mp h) i.prop⟩
    }

@[simp]
theorem toSet_inter (p q : PolyhedronDescr S n) : (p ∩ q).toSet = p.toSet ∩ q.toSet := by
  simp_rw [Set.ext_iff, Set.mem_inter_iff]
  intro x
  constructor <;> intro h
  . simp_rw [instInter, toSet, Set.mem_setOf, Pi.le_def] at h
    constructor <;> (rw [toSet, Set.mem_setOf, Pi.le_def]; intro i)
    . have := h (i.castLE $ Nat.le_add_right ..)
      simp_all [mulVec]
    . have := h ⟨p.m + i, Nat.add_lt_add_left i.prop ..⟩
      simp_all [mulVec]
  . simp_rw [instInter, toSet, Set.mem_setOf, Pi.le_def]
    intro i
    by_cases hi : i < p.m <;> simp only [hi, mulVec, ↓reduceDIte, of_apply]
    . apply h.1
    . apply h.2

inductive Comparator | le | eq | ge

/-- `LinearConstraint n` is the type of linear constraints on `n` variables. -/
structure LinearConstraint (S) (n : ℕ) where
  coefficients : Fin n → S
  comparator : Comparator
  value : S

namespace LinearConstraint

/-- Converts a linear constraint into a list o extended matrix rows for a
  linear system. -/
def toExtendedRows : LinearConstraint S n → List ((Fin n → S) × S)
| ⟨y, .le, b⟩ => [(y, b)]
| ⟨y, .eq, b⟩ => [(y, b), (-y, -b)]
| ⟨y, .ge, b⟩ => [(-y, -b)]

@[simp] lemma le_toExtendedRows
  : @toExtendedRows S _ n ⟨y, Comparator.le, b⟩ = [(y, b)] := rfl

@[simp] lemma eq_toExtendedRows
  : @toExtendedRows S _ n ⟨y, Comparator.eq, b⟩ = [(y, b), (-y, -b)] := rfl

@[simp] lemma ge_toExtendedRows
  : @toExtendedRows S _ n ⟨y, Comparator.ge, b⟩ = [(-y, -b)] := rfl

/-- valids a vector against a linear constraint. -/
def valid : LinearConstraint S n → (Fin n → S) → Prop
| ⟨y, cmp, b⟩, x =>
  let p := y ⬝ᵥ x
  match cmp with | .le => p ≤ b | .eq => p = b | .ge => p ≥ b

@[simp] lemma le_valid
  : @valid S _ n ⟨y, Comparator.le, b⟩ x = (y ⬝ᵥ x ≤ b) := rfl

@[simp] lemma eq_valid
  : @valid S _ n ⟨y, Comparator.eq, b⟩ x = (y ⬝ᵥ x = b) := rfl

@[simp] lemma ge_valid
  : @valid S _ n ⟨y, Comparator.ge, b⟩ x = (y ⬝ᵥ x ≥ b) := rfl

end LinearConstraint

/-- Constructs a polyhedron description from a list o linear `constraints`. -/
def of (constraints : List (LinearConstraint S n)) : PolyhedronDescr S n :=
  let rows := constraints.bind LinearConstraint.toExtendedRows
  ⟨rows.length, Matrix.of (Prod.fst ∘ rows.get), Prod.snd ∘ rows.get⟩

section repr
open Std.Format

instance repr [Repr S] : Repr (PolyhedronDescr S n) where
  reprPrec p _p :=
    (text "P("
      ++ (nest 2 <| reprArg p.mat ++ text ", " ++ line ++ reprArg p.vec)
      ++ text ")")

end repr

@[reducible]
instance : HasEquiv (PolyhedronDescr S n) := ⟨(·.toSet = ·.toSet)⟩

instance isSetoid (S n) [LinearOrderedField S] : Setoid (PolyhedronDescr S n) :=
  ⟨instHasEquiv.Equiv, fun _ ↦ rfl, Eq.symm, Eq.trans⟩

end PolyhedronDescr

/-- `Polyhedron S n` is the type of polyhedra in `S^n`, where `S`. -/
def Polyhedron (S : Type u₁) [LinearOrderedField S] (n : ℕ) : Type u₁ :=
  Quotient (PolyhedronDescr.isSetoid S n)

namespace Polyhedron
open Matrix PolyhedronDescr

variable {S} [LinearOrderedField S] {n : ℕ} (P : Polyhedron S n)

def ofDescr : PolyhedronDescr S n → Polyhedron S n := Quotient.mk _

/-- Notation for the polyhedron `{ x ∈ S^n | Ax ≤ b }` -/
scoped notation:max (name := matVecPolyhedron) "P(" A " , " b ")" =>
  ofDescr (⟨_, A, b⟩ : PolyhedronDescr _ _)

/-- The set of points in `P`. -/
def toSet : Set (Fin n → S) := Quotient.lift PolyhedronDescr.toSet (fun _ _ ↦ id) P

theorem toSet_inj {p q : Polyhedron S n} : p.toSet = q.toSet ↔ p = q := by
  constructor <;> intro h
  . induction p using Quotient.ind
    induction q using Quotient.ind
    rename_i p q
    rw [Quotient.eq]
    show p.toSet = q.toSet
    simp_all only [toSet, Quotient.lift_mk]
  . subst h
    rfl

instance instCoeSet : Coe (Polyhedron S n) (Set (Fin n → S)) := ⟨toSet⟩

instance : Coe (PolyhedronDescr S n) (Polyhedron S n) := ⟨ofDescr⟩

@[simp]
theorem toSet_ofDescr {d : PolyhedronDescr S n} : (ofDescr d).toSet = d.toSet := rfl

@[simp]
theorem ofDescr_eq_ofDescr {d d'  : PolyhedronDescr S n}
  : ofDescr d = ofDescr d' ↔ d.toSet = d'.toSet := by
  simp_rw [←toSet_inj, ofDescr, toSet, Quotient.lift_mk]

/-- The set of points of a polyhedron is convex. -/
theorem toSet_convex : Convex S P.toSet :=
  Quot.recOn P
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

@[reducible]
instance instMem : Membership (Fin n → S) (Polyhedron S n) := ⟨(· ∈ ·.toSet)⟩

/-- A polyhedron `P` is a polytope when it is limited, i.e. every point `x ∈ P`
  satisfies `‖x‖ ≤ α` for some `α`. -/
def IsPolytope [Norm (Fin n → S)] := ∃ α, ∀ x ∈ P, ‖x‖ ≤ α

example : Polyhedron S 2 :=
  let A : Matrix (Fin 4) (Fin 2) S :=
    !![ 1, -1;
       -1, -1;
        1,  0;
        0,  1]
  let b : Fin 4 → S := ![-2, -2, 4, 4]
  P(A, b)

/-- The empty polyhedron (`∅`). -/
def empty : Polyhedron S n :=
  let A : Matrix (Fin 2) (Fin n) S := Matrix.of $ fun
    | 0, _ => 1
    | 1, _ => -1
  let b : Fin 2 → S := ![-1, 0]
  P(A, b)

@[reducible] instance : EmptyCollection (Polyhedron S n) := ⟨empty⟩

@[reducible] instance : Bot (Polyhedron S n) := ⟨empty⟩

@[simp] theorem empty_toSet : (∅ : Polyhedron S n).toSet = ∅ := by
  change empty.toSet = ∅
  rw [empty, toSet_ofDescr, Set.eq_empty_iff_forall_not_mem]
  intro x h
  have := calc
    1 ≤ -((fun _ ↦ 1) ⬝ᵥ x) := le_neg.mpr $ h 0
    _ = (fun _ ↦ -1) ⬝ᵥ x := by simp [dotProduct]
    _ ≤ 0 := h 1
  linarith

/-- The empty polyhedron has no points. -/
theorem not_mem_empty : ∀ x, x ∉ (∅ : Polyhedron S n) := by simp [instMem]

/-- The universe polyhedron (`S^n`). -/
def univ : Polyhedron S n := P(0, ![])

instance : Top (Polyhedron S n) := ⟨univ⟩

@[simp] theorem univ_toSet : (⊤ : Polyhedron S n).toSet = Set.univ := by
  show univ.toSet = Set.univ
  simp [univ]

/-- The empty polyhedron contains all points. -/
theorem mem_univ : ∀ x, x ∈ (⊤ : Polyhedron S n) := by simp [instMem]

def ofConstraints (constraints : List (LinearConstraint S n)) :=
  ofDescr $ PolyhedronDescr.of constraints

section Notation

open Lean.Parser
open Lean.Elab.Term

/-- Syntax for addressing variables in linear constraints.

  `x_[n]` is shorthand for `Pi.single n 1`. -/
notation "x_[" n "]" => Pi.single n 1

/-- Syntax category for linear constraints used to define polyhedra. -/
declare_syntax_cat linConstraint
syntax:60 term:61 " ≤ " term : linConstraint
syntax:60 term:61 " = " term : linConstraint
syntax:60 term:61 " ≥ " term : linConstraint

/-- Syntax for declaring polyhedra as systems of linear constraints. -/
syntax:100 (name := systemPolyhedron)
  "P" ("[" term:90 "^" term "]")? "{" linConstraint,*,? "}" : term
macro_rules
  | `(P[$t^$n]{$[$constraints],*}) => `((P{$constraints,*} : Polyhedron $t $n))
  | `(P{$[$constraints],*}) => do
    let constraints ← constraints.mapM (fun
      | `(linConstraint| $x:term ≤ $y:term) => `(⟨$x, Comparator.le, $y⟩)
      | `(linConstraint| $x:term = $y:term) => `(⟨$x, Comparator.eq, $y⟩)
      | `(linConstraint| $x:term ≥ $y:term) => `(⟨$x, Comparator.ge, $y⟩)
      | _ => Lean.Macro.throwUnsupported)
    `(ofConstraints [$constraints,*])

example := P[ℚ^2]{2 • x_[1] ≤ 1}
example : Polyhedron S 2 := P{2 • x_[1] ≤ 1, x_[0] + x_[1] = 0}

end Notation

section toSet_ofConstraints
open LinearConstraint

-- FIXME: there must be a better way?
private lemma prod_eq : p.1 = a ∧ p.2 = b ↔ p = (a, b) := by
  obtain ⟨fst, snd⟩ := p
  simp_all only [Prod.mk.injEq]

private lemma le_lemma
  {constraints : List (LinearConstraint S n)} {y : Fin n → S} {b : S}
  : ⟨y, Comparator.le, b⟩ ∈ constraints →
    ∃ i, (of constraints).mat i = y ∧ (of constraints).vec i = b := by
  let rows := constraints.bind toExtendedRows
  intro h
  show ∃ i : Fin rows.length, rows[i].1 = y ∧ rows[i].2 = b
  simp_rw [prod_eq]
  apply List.mem_iff_get.mp
  rw [List.mem_bind]
  exact ⟨_, h, by simp [toExtendedRows]⟩

private lemma ge_lemma
  {constraints : List (LinearConstraint S n)} {y : Fin n → S} {b : S}
  : ⟨y, Comparator.ge, b⟩ ∈ constraints →
    ∃ i, (of constraints).mat i = -y ∧ (of constraints).vec i = -b := by
  let rows := constraints.bind toExtendedRows
  intro h
  show ∃ i : Fin rows.length, rows[i].1 = -y ∧ rows[i].2 = -b
  simp_rw [prod_eq]
  apply List.mem_iff_get.mp
  rw [List.mem_bind]
  exact ⟨_, h, by simp [toExtendedRows]⟩

private lemma eq_lemma
  {constraints : List (LinearConstraint S n)} {y : Fin n → S} {b : S}
  : ⟨y, Comparator.eq, b⟩ ∈ constraints →
      (∃ i, (of constraints).mat i = y ∧ (of constraints).vec i = b)
    ∧ (∃ i, (of constraints).mat i = -y ∧ (of constraints).vec i = -b) := by
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

@[simp] theorem mem_ofConstraints (constraints : List (LinearConstraint S n))
  : ∀ x, x ∈ ofConstraints constraints ↔ ∀ c ∈ constraints, c.valid x := by
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
@[simp] theorem toSet_ofConstraints (constraints : List (LinearConstraint S n))
  : (ofConstraints constraints).toSet = { x | ∀ constr ∈ constraints, constr.valid x } :=
  Set.ext_iff.mpr (mem_ofConstraints _)

end toSet_ofConstraints

@[reducible] instance : Inter (Polyhedron S n) where
  inter := Quotient.lift₂ (ofDescr $ · ∩ ·) $ by
    intro a b a' b' ha hb
    simp_rw [ofDescr_eq_ofDescr, toSet_inter]
    change a.toSet = a'.toSet at ha
    change b.toSet = b'.toSet at hb
    simp_all only

@[simp] theorem toSet_inter (p q : Polyhedron S n) : (p ∩ q).toSet = p.toSet ∩ q.toSet :=
  Quotient.inductionOn₂ p q PolyhedronDescr.toSet_inter

@[simp]
theorem mem_inter {p q : Polyhedron S n} {x : Fin n → S} : x ∈ p ∩ q ↔ x ∈ p ∧ x ∈ q := by
  induction p using Quotient.ind
  induction q using Quotient.ind
  simp only [instMem, toSet_inter, Set.mem_inter_iff]

@[reducible] instance : HasSubset (Polyhedron S n) := ⟨(·.toSet ⊆ ·.toSet)⟩

theorem subset_iff {p q : Polyhedron S n} : p ⊆ q ↔ ∀ x, x ∈ p → x ∈ q := by
  constructor <;> intro h <;> exact h

theorem empty_subset (p : Polyhedron S n) : ∅ ⊆ p := by simp [subset_iff, not_mem_empty]

theorem subset_univ (p : Polyhedron S n) : p ⊆ ⊤ := by simp [subset_iff, mem_univ]

@[reducible] instance : SemilatticeInf (Polyhedron S n) where
  inf := (· ∩ ·)
  le := (· ⊆ ·)
  le_refl p := subset_refl p.toSet
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h h' := toSet_inj.mp $ subset_antisymm h h'
  inf_le_left _ _ _ h := And.left $ mem_inter.mp h
  inf_le_right _ _ _ h := And.right $ mem_inter.mp h
  le_inf _ _ _ h h' _ hx := mem_inter.mpr $ And.intro (h hx) (h' hx)
