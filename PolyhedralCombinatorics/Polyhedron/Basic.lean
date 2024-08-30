import PolyhedralCombinatorics.Polyhedron.Defs

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sum.Order

import Mathlib.Tactic.LiftLets
import Mathlib.Tactic.HelpCmd

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ} (p q r : Polyhedron 𝔽 n)

@[simp] theorem toSet_ofLinearSystem {d : LinearSystem 𝔽 n} : (ofLinearSystem d).toSet = d.solutions := rfl

@[simp] theorem empty_toSet : (∅ : Polyhedron 𝔽 n).toSet = ∅ := by
  change empty.toSet = ∅
  simp [empty, Set.eq_empty_iff_forall_not_mem, Pi.le_def]

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

section Projection

/-- A projection of `S` over `H` in the direction of `c` is a polyhedron such
  that every point in `P` is in `R` and `x + α c ∈ Q`, for some `α`. -/
def Projection (S H : Polyhedron 𝔽 n) (c : Fin n → 𝔽) :=
  { P : Polyhedron 𝔽 n // ∀ x, x ∈ P ↔ x ∈ H ∧ ∃ α : 𝔽, x + α • c ∈ S }

def openProjection' (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) : LinearSystem 𝔽 n :=
  let N : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c < 0 }
  let Z : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c = 0 }
  let P : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c > 0 }
  let R : Finset (Fin S.m ⊕ₗ Fin S.m ×ₗ Fin S.m) :=
    Z.map ⟨_, Sum.inl_injective⟩ ∪ (N ×ˢ P).map ⟨_, Sum.inr_injective⟩
  let p := R.orderIsoOfFin rfl
  let D : Matrix (Fin R.card) (Fin n) 𝔽 := Matrix.of fun i ↦
    match (p i).1 with
    | .inl s => S.mat s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t
  let d : Fin (R.card) → 𝔽 := fun i ↦
    match (p i).1 with
    | .inl s => S.vec s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.vec s - (S.mat s ⬝ᵥ c) • S.vec t
  of D d

lemma solutions_openProjection' (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽)
  : (openProjection' S c).solutions = { x | ∃ α : 𝔽, x + α • c ∈ S.solutions } := by
  unfold openProjection'
  lift_lets
  extract_lets N Z P R p D d
  ext x
  simp_rw [Set.mem_setOf]
  let α : Fin S.m → 𝔽 := fun i ↦ (S.vec i - S.mat i ⬝ᵥ x) / (S.mat i ⬝ᵥ c)
  let L : WithBot 𝔽 :=
    if h : N.Nonempty then
      (Finset.image α N).max' (Finset.image_nonempty.mpr h)
    else
      ⊥
  let U : WithTop 𝔽 :=
    if h : P.Nonempty then
      (Finset.image α P).min' (Finset.image_nonempty.mpr h)
    else
      ⊤
  have lemma_c1
    : x ∈ (of D d).solutions →
      L.map WithTop.some ≤ .some U ∧ ∀ {α' : 𝔽}, L ≤ α' → α' ≤ U → x + α' • c ∈ S.solutions := by
    intro x_mem_PDd
    rw [mem_solutions_of, Pi.le_def] at x_mem_PDd
    have L_le_U : WithBot.map WithTop.some L ≤ U := by
      by_cases hN : N.Nonempty <;> by_cases hP : P.Nonempty
      all_goals (
        unfold_let U L
        simp only [
          hN, hP, reduceDIte,
          WithBot.map_bot, WithBot.coe_top, WithBot.map_coe, WithBot.coe_le_coe,
          WithTop.coe_le_coe, bot_le, le_top
        ]
      )
      simp_rw [
        Finset.le_min'_iff, Finset.max'_le_iff, Finset.mem_image,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂
      ]
      intro t ht s hs
      unfold_let P N α at hs ht ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ht ⊢
      rw [←neg_le_neg_iff, ←neg_div, ←div_neg, div_le_div_iff ht (neg_pos.mpr hs), neg_mul_neg]
      have h' := x_mem_PDd $ p.symm ⟨
        .inr (s, t),
        by
          apply Finset.mem_union_right
          apply Finset.mem_map_of_mem
          apply Finset.mem_product.mpr
          simp only
          constructor <;> rw [Finset.mem_filter] <;> simp [ht, hs]
      ⟩
      unfold_let D d at h'
      simp_rw [
        mulVec, of_apply, OrderIso.apply_symm_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ←Pi.sub_def, ←Pi.mul_def,
        ←smul_eq_mul
      ] at h'
      change ((S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t) ⬝ᵥ x ≤ _ at h'
      simp_rw [
        sub_dotProduct,
        sub_le_sub_iff,
        add_comm,
        ←sub_le_sub_iff,
        smul_dotProduct,
        ←smul_sub
      ] at h'
      simp_rw [mul_comm, ←smul_eq_mul, h']
    apply And.intro L_le_U
    simp only [mem_solutions, Pi.le_def]
    intro α hl hu i
    rcases lt_trichotomy (S.mat i ⬝ᵥ c) 0 with neg | zero | pos
    rotate_left
    . simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, mulVec, zero, smul_zero, add_zero]
      have mem_Z : i ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, zero⟩
      have h' := x_mem_PDd $ p.symm ⟨.inl i, Finset.mem_union_left _ $ Finset.mem_map_of_mem _ mem_Z⟩
      unfold_let D d at h'
      simp_rw [mulVec, of_apply, OrderIso.apply_symm_apply] at h'
      assumption
    . have : i ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, pos⟩
      have : P.Nonempty := ⟨_, this⟩
      unfold_let U at hu
      simp only [this, ↓reduceDIte, WithTop.coe_le_coe, Finset.le_min'_iff, Finset.mem_image,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hu
      unfold_let at hu
      simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hu i pos
      rw [le_div_iff pos, le_sub_iff_add_le, add_comm] at this
      assumption
    . have : i ∈ N := Finset.mem_filter.mpr ⟨Finset.mem_univ _, neg⟩
      have : N.Nonempty := ⟨_, this⟩
      unfold_let L at hl
      simp only [this, ↓reduceDIte, WithBot.coe_le_coe, Finset.max'_le_iff, Finset.mem_image,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hl
      unfold_let at hl
      simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hl i neg
      rw [div_le_iff_of_neg neg, le_sub_iff_add_le, add_comm] at this
      assumption
  have lemma_c2 : ∀ {α' : 𝔽}, x + α' • c ∈ S.solutions → x ∈ (of D d).solutions := by
    intro α' h
    simp only [mem_solutions_of, mem_solutions, Pi.le_def] at h ⊢
    intro i
    unfold_let D d
    simp_rw [mulVec, of_apply]
    rcases hr : (p i).1 with s | ⟨s, t⟩ <;> simp only
    . have hs : s ∈ Z := by
        have mem_R : .inl s ∈ R := hr ▸ (p i).2
        simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, and_false,
          exists_false, or_false, R] at mem_R
        obtain ⟨_, h₁, h₂⟩ := mem_R
        rw [Sum.inl.inj_iff] at h₂
        subst h₂
        assumption
      simp_rw [Z, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      have := h s
      simp_rw [mulVec_add, mulVec_smul] at this
      unfold mulVec at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hs, mul_zero, add_zero] at this
      assumption
    . have mem_R : .inr ⟨s, t⟩ ∈ R := hr ▸ (p i).2
      simp only [Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, and_false,
        exists_false, false_or, R] at mem_R
      obtain ⟨_, h₁, h₂⟩ := mem_R
      rw [Sum.inr.inj_iff] at h₂
      subst h₂
      have hs : s ∈ N := (Finset.mem_product.mp h₁).1
      have ht : t ∈ P := (Finset.mem_product.mp h₁).2
      simp_rw [N, P, Finset.mem_filter, Finset.mem_univ, true_and] at hs ht
      have h₁ := h s
      have h₂ := h t
      have : ((S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t) ⬝ᵥ (α' • c) = 0 := by
        simp_rw [sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        conv =>
          lhs
          congr <;> rw [mul_comm, mul_assoc]
          . rfl
          . rhs
            rw [mul_comm]
        apply sub_self
      rw [←add_zero (_ ⬝ᵥ x), ←this, ←dotProduct_add]
      simp_rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      apply sub_le_sub
      . rw [mul_le_mul_left ht]
        exact h₁
      . rw [mul_le_mul_left_of_neg hs]
        exact h₂
  constructor <;> intro h
  . have ⟨h₁, h₂⟩ := lemma_c1 h
    suffices h' : ∃ α : 𝔽, L ≤ α ∧ α ≤ U by
      obtain ⟨_, hl, hu⟩ := h'
      exact ⟨_, h₂ hl hu⟩
    match L, U with
    | ⊥, ⊤ => exact ⟨0, bot_le, le_top⟩
    | ⊥, .some U => exact ⟨U, bot_le, le_rfl⟩
    | .some L, ⊤ => exact ⟨L, le_rfl, le_top⟩
    | .some L, .some U =>
      simp_rw [WithBot.map_coe, WithBot.coe_le_coe, WithTop.coe_le_coe] at h₁
      obtain ⟨_, hl, hu⟩ := Set.nonempty_Icc.mpr h₁
      exact ⟨_, WithBot.coe_le_coe.mpr hl, WithTop.coe_le_coe.mpr hu⟩
  . obtain ⟨α, h⟩ := h
    exact lemma_c2 h

def openProjection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  Quotient.liftOn P
    (fun S ↦ openProjection' S c)
    (fun a b h ↦ toSet_inj.mp $
      (solutions_openProjection' a _).trans (h ▸ solutions_openProjection' b _).symm)

theorem mem_openProjection {P : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : x ∈ P.openProjection c ↔ ∃ α : 𝔽, x + α • c ∈ P := by
  induction P using Quotient.ind
  unfold openProjection
  simp_rw [
    Quotient.lift_mk,
    mem_def,
    toSet,
    ofLinearSystem,
    Quotient.lift_mk,
    solutions_openProjection',
    Set.mem_setOf
  ]

def projection (S H : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Projection S H c :=
  ⟨H ∩ S.openProjection c, by
    simp_rw [mem_inter, and_congr_right_iff]
    intros
    exact mem_openProjection⟩

instance {S H : Polyhedron 𝔽 n} : Unique (Projection S H c) where
  default := projection S H c
  uniq p := Subtype.val_inj.mp $ ext_iff.mpr fun x ↦ (p.2 x).trans ((projection ..).2 x).symm

end Projection
