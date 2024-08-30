import PolyhedralCombinatorics.Polyhedron.Basic
import PolyhedralCombinatorics.Polyhedron.Notation

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sum.Order

import Mathlib.Tactic.LiftLets

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

private lemma Finset.mem_filter_univ {α} [Fintype α] {x : α} {p : α → Prop} [DecidablePred p]
  : x ∈ ({ x | p x } : Finset α) ↔ p x := by
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and]

namespace LinearSystem
open Matrix Finset

def directionalProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) : LinearSystem 𝔽 n :=
  let N : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c < 0 }
  let Z : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c = 0 }
  let P : Finset (Fin S.m) := { i | S.mat i ⬝ᵥ c > 0 }
  let R : Finset (Fin S.m ⊕ₗ Fin S.m ×ₗ Fin S.m) := Z.image Sum.inl ∪ (N ×ˢ P).image Sum.inr
  let p : Fin R.card ≃o R := R.orderIsoOfFin rfl
  let D : Matrix (Fin R.card) (Fin n) 𝔽 := Matrix.of fun i ↦
    match (p i).1 with
    | .inl s => S.mat s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t
  let d : Fin (R.card) → 𝔽 := fun i ↦
    match (p i).1 with
    | .inl s => S.vec s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.vec s - (S.mat s ⬝ᵥ c) • S.vec t
  of D d

lemma solutions_directionalProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽)
  : (directionalProjection S c).solutions = { x | ∃ α : 𝔽, x + α • c ∈ S.solutions } := by
  unfold directionalProjection
  lift_lets
  extract_lets N Z P R p D d
  ext x
  simp_rw [Set.mem_setOf]
  let α : Fin S.m → 𝔽 := fun i ↦ (S.vec i - S.mat i ⬝ᵥ x) / (S.mat i ⬝ᵥ c)
  let L : WithBot 𝔽 :=
    if h : N.Nonempty then (N.image α).max' $ image_nonempty.mpr h else ⊥
  let U : WithTop 𝔽 :=
    if h : P.Nonempty then (P.image α).min' $ image_nonempty.mpr h else ⊤
  constructor <;> intro h
  . rw [mem_solutions_of, Pi.le_def] at h
    have L_le_U : L.map .some ≤ .some U := by
      unfold_let U L
      split <;> split
      case isFalse.isFalse | isFalse.isTrue => apply bot_le
      case isTrue.isFalse => apply le_top
      simp_rw [WithBot.map_coe, WithBot.coe_le_coe, WithTop.coe_le_coe,
        le_min'_iff, max'_le_iff, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro t ht s hs
      unfold_let P N α at hs ht ⊢
      simp only [mem_filter_univ] at hs ht ⊢
      have h' := h $ p.symm ⟨.inr (s, t), by
          apply mem_union_right
          apply mem_image_of_mem
          apply mem_product.mpr
          constructor <;> rw [mem_filter] <;> simp [ht, hs]⟩
      unfold_let D d at h'
      simp only [mulVec, of_apply, OrderIso.apply_symm_apply] at h'
      change ((S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t) ⬝ᵥ x ≤ _ at h'
      simp_rw [sub_dotProduct, sub_le_sub_iff, add_comm, ←sub_le_sub_iff, smul_dotProduct, ←smul_sub] at h'
      rw [←neg_le_neg_iff, ←neg_div, ←div_neg, div_le_div_iff ht (neg_pos.mpr hs), neg_mul_neg]
      simp_rw [mul_comm, ←smul_eq_mul, h']
    have : ∀ {α' : 𝔽}, L ≤ α' → α' ≤ U → x + α' • c ∈ S.solutions := by
      simp only [mem_solutions, Pi.le_def]
      intro α hl hu i
      rcases lt_trichotomy (S.mat i ⬝ᵥ c) 0 with neg | zero | pos
      rotate_left
      . simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, mulVec, zero, smul_zero, add_zero]
        have mem_Z : i ∈ Z := mem_filter.mpr ⟨mem_univ _, zero⟩
        have h' := h $ p.symm ⟨.inl i, mem_union_left _ $ mem_image_of_mem _ mem_Z⟩
        unfold_let D d at h'
        simp_rw [mulVec, of_apply, OrderIso.apply_symm_apply] at h'
        assumption
      . have : i ∈ P := mem_filter.mpr ⟨mem_univ _, pos⟩
        have : P.Nonempty := ⟨_, this⟩
        unfold_let U at hu
        simp only [this, ↓reduceDIte, WithTop.coe_le_coe, le_min'_iff, mem_image,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hu
        unfold_let at hu
        simp only [gt_iff_lt, mem_filter, mem_univ, true_and] at hu
        simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hu i pos
        rw [le_div_iff₀ pos, le_sub_iff_add_le, add_comm] at this
        assumption
      . have : i ∈ N := mem_filter.mpr ⟨mem_univ _, neg⟩
        have : N.Nonempty := ⟨_, this⟩
        unfold_let L at hl
        simp only [this, ↓reduceDIte, WithBot.coe_le_coe, max'_le_iff, mem_image,
          forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hl
        unfold_let at hl
        simp only [gt_iff_lt, mem_filter, mem_univ, true_and] at hl
        simp_rw [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hl i neg
        rw [div_le_iff_of_neg neg, le_sub_iff_add_le, add_comm] at this
        assumption
    suffices h' : ∃ α : 𝔽, L ≤ α ∧ α ≤ U by obtain ⟨_, hl, hu⟩ := h'; exact ⟨_, this hl hu⟩
    match L, U with
    | ⊥, ⊤ => exact ⟨0, bot_le, le_top⟩
    | ⊥, .some U => exact ⟨U, bot_le, le_rfl⟩
    | .some L, ⊤ => exact ⟨L, le_rfl, le_top⟩
    | .some L, .some U =>
      simp_rw [WithBot.map_coe, WithBot.coe_le_coe, WithTop.coe_le_coe] at L_le_U
      obtain ⟨_, hl, hu⟩ := Set.nonempty_Icc.mpr L_le_U
      exact ⟨_, WithBot.coe_le_coe.mpr hl, WithTop.coe_le_coe.mpr hu⟩
  . obtain ⟨α', h⟩ := h
    simp only [mem_solutions_of, mem_solutions, Pi.le_def] at h ⊢
    intro i
    unfold_let D d
    simp_rw [mulVec, of_apply]
    rcases hr : (p i).1 with s | ⟨s, t⟩ <;> simp only
    . have hs : s ∈ Z := by
        have mem_R : .inl s ∈ R := hr ▸ (p i).2
        simp only [mem_union, mem_image, Function.Embedding.coeFn_mk, and_false,
          exists_false, or_false, R] at mem_R
        obtain ⟨_, h₁, h₂⟩ := mem_R
        rw [Sum.inl.inj_iff] at h₂
        subst h₂
        assumption
      simp_rw [Z, mem_filter, mem_univ, true_and] at hs
      have := h s
      simp_rw [mulVec_add, mulVec_smul] at this
      unfold mulVec at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [hs, mul_zero, add_zero] at this
      assumption
    . have mem_R : .inr ⟨s, t⟩ ∈ R := hr ▸ (p i).2
      simp only [mem_union, mem_image, Function.Embedding.coeFn_mk, and_false,
        exists_false, false_or, R] at mem_R
      obtain ⟨_, h₁, h₂⟩ := mem_R
      rw [Sum.inr.inj_iff] at h₂
      subst h₂
      have hs : s ∈ N := (mem_product.mp h₁).1
      have ht : t ∈ P := (mem_product.mp h₁).2
      simp_rw [N, P, mem_filter, mem_univ, true_and] at hs ht
      have : ((S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t) ⬝ᵥ (α' • c) = 0 := by
        simp_rw [sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        conv =>
          lhs; congr <;> rw [mul_comm, mul_assoc]
          . rfl
          . rhs; rw [mul_comm]
        apply sub_self
      rw [←add_zero (_ ⬝ᵥ x), ←this, ←dotProduct_add]
      simp_rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
      apply sub_le_sub
      . rw [mul_le_mul_left ht]; exact h s
      . rw [mul_le_mul_left_of_neg hs]; exact h t

end LinearSystem

namespace Polyhedron
open Matrix LinearSystem

def directionalProjection (p : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  Quotient.liftOn p
    (fun S ↦ LinearSystem.directionalProjection S c)
    (fun a b h ↦ toSet_inj.mp $
      (solutions_directionalProjection a _).trans (h ▸ solutions_directionalProjection b _).symm)

@[simp]
theorem mem_directionalProjection {p : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : x ∈ p.directionalProjection c ↔ ∃ α : 𝔽, x + α • c ∈ p := by
  induction p using Quotient.ind
  unfold directionalProjection
  simp_rw [Quotient.lift_mk, mem_ofLinearSystem, solutions_directionalProjection, Set.mem_setOf]
  rfl

def projection (S H : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  H ∩ S.directionalProjection c

@[simp] theorem mem_projection {S H : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : x ∈ S.projection H c ↔ x ∈ H ∧ ∃ α : 𝔽, x + α • c ∈ S := by simp [projection]

@[simp] theorem subset_directionalProjection {S : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : S ⊆ S.directionalProjection c := by
  intro x
  rw [mem_directionalProjection]
  intro x_mem_S
  exists 0
  rw [zero_smul, add_zero]
  assumption

theorem projection_self (p : Polyhedron 𝔽 n) (c) : p.projection p c = p := by
  apply subset_antisymm
  . apply inter_subset_left
  . apply subset_inter
    . apply subset_refl
    . apply subset_directionalProjection

def fourierMotzkin (p : Polyhedron 𝔽 n) (j : Fin n) := p.projection !P{x_[j] = 0} x_[j]

theorem mem_fourierMotzkin (p : Polyhedron 𝔽 n) (j : Fin n) :
  x ∈ p.fourierMotzkin j ↔ x j = 0 ∧ ∃ (α : 𝔽), x + Pi.single j α ∈ p := by
  simp_rw [
    fourierMotzkin, mem_projection, mem_ofConstraints,
    List.mem_singleton, forall_eq, LinearConstraint.eq_valid,
    single_dotProduct, one_mul, and_congr_right_iff,
    ←Pi.single_smul, smul_eq_mul, mul_one, implies_true
  ]

theorem coord_zero_of_mem_fourierMotzkin {p : Polyhedron 𝔽 n} {j : Fin n} {x : Fin n → 𝔽}
  (h : x ∈ p.fourierMotzkin j) : x j = 0 := by
  rw [mem_fourierMotzkin] at h
  exact h.1

theorem directionalProjection_eq_empty_iff (p : Polyhedron 𝔽 n) (c)
  : p.directionalProjection c = ∅ ↔ p = ∅ := by
  constructor <;> intro h
  . have := projection_self p c
    simp_rw [Polyhedron.ext_iff, mem_projection] at this
    simp_rw [eq_empty_iff, mem_directionalProjection] at h ⊢
    simp_all
  . simp_rw [eq_empty_iff, mem_directionalProjection]
    simp_all [not_mem_empty]

def recElimDimensions (p : Polyhedron 𝔽 n) {k : ℕ} (h : k ≤ n) :=
  match k with
  | 0 => p
  | k + 1 => (p.recElimDimensions $ le_of_add_le_left h).fourierMotzkin ⟨k, h⟩

lemma recElimDimensions_lemma {p : Polyhedron 𝔽 n} {k : ℕ} (h : k ≤ n) :
  ∀ ⦃x⦄, x ∈ p.recElimDimensions h → ∀ ⦃j : Fin n⦄, j < k → x j = 0 := by
  unfold recElimDimensions
  split
  . simp
  next k h' =>
    simp only [mem_fourierMotzkin]
    intro x ⟨h₁, h₂⟩
    obtain ⟨α, h₃⟩ := h₂
    intro j hj
    rcases eq_or_lt_of_le hj with eq | lt
    . simp only [Nat.succ_eq_add_one, add_left_inj] at eq
      simp_rw [←eq] at h₁
      exact h₁
    . simp only [Nat.succ_eq_add_one, add_lt_add_iff_right] at lt
      have := recElimDimensions_lemma _ h₃ lt
      rw [Pi.add_apply, Pi.single_apply] at this
      have : j ≠ ⟨k, h'⟩ := by
        rw [ne_eq, Fin.eq_mk_iff_val_eq]
        exact lt.ne
      simp_all only [Nat.succ_eq_add_one, ite_false, add_zero, ne_eq]

-- theorem recElimDimensions_eq_empty_iff (p : Polyhedron 𝔽 n) {k : ℕ} (hk : k ≤ n)
--   : p.recElimDimensions h = ∅ ↔ p = ∅ := by
--   constructor <;> intro h
--   . unfold recElimDimensions at h
--     split at h
--     . assumption
--     . sorry
--       -- simp_rw [eq_empty_iff, mem_fourierMotzkin, not_and, not_exists] at h ⊢
--       -- intro x
--       -- replace h := h (Function.update x _ 0) (Function.update_same ..) 0
--       -- rw [Pi.single_zero, add_zero] at h
--       -- sorry
--   . unfold recElimDimensions
--     split
--     . assumption
--     . ext
--       simp_rw [mem_fourierMotzkin, not_mem_empty, iff_false, not_and, not_exists]
--       intro h x
--       suffices p.recElimDimensions _ = ∅ by
--         rw [this]
--         apply not_mem_empty
--       apply (p.recElimDimensions_eq_empty_iff hk).mpr
--       assumption

-- lemma mem_recElimDimensions_lemma2 {p : Polyhedron 𝔽 n} {k : ℕ} (h : k ≤ n) :
--   x ∈ p.recElimDimensions h ↔
--   (∀ ⦃j : Fin n⦄, j < k → x j = 0) ∧ ∃ x', (∀ ⦃i : Fin n⦄, i ≥ k → x' i = 0) ∧ x + x' ∈ p := by
--   unfold recElimDimensions
--   split
--   . simp only [not_lt_zero', false_implies, implies_true, ge_iff_le, zero_le, true_implies,
--     true_and]
--     constructor <;> intro h
--     . exists 0
--       simp_all
--     . obtain ⟨x', h₁, h₂⟩ := h
--       have : x' = 0 := funext h₁
--       subst this
--       simp_all
--   next k h' =>
--     simp only [mem_fourierMotzkin]
--     constructor <;> intro ⟨h₁, h₂⟩
--     . constructor
--       . intro j hj
--         rcases eq_or_lt_of_le hj with eq | lt
--         . simp only [Nat.succ_eq_add_one, add_left_inj] at eq
--           simp_rw [←eq] at h₁
--           exact h₁
--         . obtain ⟨α, h₃⟩ := h₂
--           simp_rw [mem_recElimDimensions_lemma2] at h₃
--           obtain ⟨h₄, h₅⟩ := h₃

--           sorry
--       . sorry
--     . constructor
--       . sorry
--       . sorry

end Polyhedron
