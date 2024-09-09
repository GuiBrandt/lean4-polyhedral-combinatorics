import PolyhedralCombinatorics.Polyhedron.Basic
import PolyhedralCombinatorics.Polyhedron.Notation

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sum.Order

import Mathlib.Tactic.LiftLets

import Utils.IsEmpty

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

private lemma Finset.mem_filter_univ {α} [Fintype α] {x : α} {p : α → Prop} [DecidablePred p]
  : x ∈ ({ x | p x } : Finset α) ↔ p x := by
  simp_rw [Finset.mem_filter, Finset.mem_univ, true_and]

namespace LinearSystem
open Matrix Finset

def projection (P : LinearSystem 𝔽 n) (c : Fin n → 𝔽) := { x | ∃ α : 𝔽, x + α • c ∈ P.solutions }

theorem projection_neg (P : LinearSystem 𝔽 n) (c : Fin n → 𝔽) : P.projection (-c) = P.projection c := by
  simp only [projection, Set.ext_iff, Set.mem_setOf]
  intro x
  constructor
  all_goals (
    intro h
    obtain ⟨α, h⟩ := h
    exists -α
    simp_all
  )

theorem projection_concat_comm {P Q : LinearSystem 𝔽 n} {c}
  : projection (concat P Q) c = projection (concat Q P) c := by
  unfold projection
  simp_rw [concat_solutions, Set.inter_comm]

@[simp] lemma mem_projection {P : LinearSystem 𝔽 n}
  : x ∈ P.projection c ↔ ∃ α : 𝔽, x + α • c ∈ P.solutions := Set.mem_setOf

@[simp]
lemma projection_semiSpace_orthogonal (a : Fin n → 𝔽) (b : 𝔽) (c : Fin n → 𝔽) (h : a ⬝ᵥ c = 0)
  : projection (semiSpace a b) c = (semiSpace a b).solutions := by
  simp_rw [projection, Set.ext_iff, Set.mem_setOf, mem_semiSpace]
  intro x
  constructor
  . intro ⟨_, h'⟩
    simp_rw [dotProduct_add, dotProduct_smul, h, smul_zero, add_zero] at h'
    assumption
  . intro h
    exists 0
    simp [h]

@[simp]
lemma projection_semiSpace_nonorthogonal (a : Fin n → 𝔽) (b : 𝔽) (c : Fin n → 𝔽) (h : a ⬝ᵥ c ≠ 0)
  : projection (semiSpace a b) c = Set.univ := by
  simp_rw [projection, mem_semiSpace, Set.eq_univ_iff_forall, Set.mem_setOf]
  intro x
  simp_rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  exists (b - a ⬝ᵥ x)/(a ⬝ᵥ c)
  simp_rw [div_mul_cancel₀ _ h, add_sub_cancel]
  rfl

@[simp] theorem proj_concat_semiSpace_orthogonal
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c = 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (concat H₁ H₂) c = (concat H₁ H₂).solutions := by
  ext x
  simp_all

@[simp] theorem proj_concat_semiSpace_orthogonal_left
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c ≠ 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (concat H₁ H₂) c = H₁.solutions := by
  ext x
  simp_rw [mem_projection, concat_solutions, Set.mem_inter_iff, mem_semiSpace, dotProduct_add,
    dotProduct_smul, h₁, smul_zero, add_zero, exists_and_left, and_iff_left_iff_imp]
  intro
  exists (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
  simp_rw [smul_eq_mul, div_mul_cancel₀ _ h₂, add_sub_cancel]
  rfl

@[simp] theorem proj_concat_semiSpace_orthogonal_right
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : a₁ ⬝ᵥ c ≠ 0) (h₂ : a₂ ⬝ᵥ c = 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (concat H₁ H₂) c = H₂.solutions := by
  extract_lets H₁ H₂
  rw [projection_concat_comm]
  exact proj_concat_semiSpace_orthogonal_left _ _ b₂ b₁ _ h₂ h₁

@[simp] theorem proj_concat_semiSpace_nonorthogonal_pos
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : 0 < a₂ ⬝ᵥ c)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (concat H₁ H₂) c = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  simp_rw [mem_projection, concat_solutions, Set.mem_inter_iff, mem_semiSpace, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  let l := (b₁ - a₁ ⬝ᵥ x)/(a₁ ⬝ᵥ c)
  let r := (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
  exists min l r
  constructor
  . calc
      _ ≤ a₁ ⬝ᵥ x + l * a₁ ⬝ᵥ c := by
        rw [add_le_add_iff_left, mul_le_mul_right h₁]
        apply min_le_left
      _ = _ := by
        simp_rw [l, div_mul_cancel₀ _ h₁.ne.symm, add_sub_cancel]
  . calc
      _ ≤ a₂ ⬝ᵥ x + r * a₂ ⬝ᵥ c := by
        rw [add_le_add_iff_left, mul_le_mul_right h₂]
        apply min_le_right
      _ = _ := by
        simp_rw [r, div_mul_cancel₀ _ h₂.ne.symm, add_sub_cancel]

@[simp] theorem proj_concat_semiSpace_nonorthogonal_neg
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : a₂ ⬝ᵥ c < 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (concat H₁ H₂) c = Set.univ := by
  extract_lets
  rw [←projection_neg]
  apply proj_concat_semiSpace_nonorthogonal_pos <;> simp_all

@[simp] theorem proj_concat_semiSpace_nonorthogonal_neg_pos
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : 0 < a₂ ⬝ᵥ c)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    let a₃ := (a₂ ⬝ᵥ c) • a₁ - (a₁ ⬝ᵥ c) • a₂
    let b₃ := (a₂ ⬝ᵥ c) * b₁ - (a₁ ⬝ᵥ c) * b₂
    projection (concat H₁ H₂) c = (semiSpace a₃ b₃).solutions := by
  ext x
  simp_rw [mem_projection, concat_solutions, Set.mem_inter_iff, mem_semiSpace]
  constructor
  . intro ⟨α, h₁', h₂'⟩
    simp_rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_le_sub_iff, add_comm,
      ←sub_le_sub_iff, ←mul_sub]
    rw [dotProduct_add, dotProduct_smul, ←le_sub_iff_add_le', smul_eq_mul] at h₁' h₂'
    rw [←div_le_iff_of_neg' h₁]
    calc
      _ ≤ α * a₂ ⬝ᵥ c := by
        rw [mul_comm, mul_div_assoc, ←div_le_iff_of_neg]
        . calc
          _ ≤ α * a₁ ⬝ᵥ c := by
            rw [div_div_eq_mul_div, mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ h₂.ne.symm]
          _ ≤ _ := h₁'
        . simp [div_neg_iff, h₁, h₂]
      _ ≤ _ := h₂'
  . intro h
    simp_rw [sub_dotProduct, smul_dotProduct, sub_le_sub_iff, add_comm, ←sub_le_sub_iff,
      smul_eq_mul, ←mul_sub, mul_comm, ←div_le_iff₀ h₂, mul_div_assoc, ←div_le_iff_of_neg' h₁] at h
    exists (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    constructor
    . apply add_le_of_le_sub_left
      rw [←div_le_iff_of_neg h₁]
      assumption
    . simp [div_mul_cancel₀ _ h₂.ne.symm]

@[simp] theorem proj_concat_semiSpace_nonorthogonal_pos_neg
  (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
  (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : a₂ ⬝ᵥ c < 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    let a₃ := (a₁ ⬝ᵥ c) • a₂ - (a₂ ⬝ᵥ c) • a₁
    let b₃ := (a₁ ⬝ᵥ c) * b₂ - (a₂ ⬝ᵥ c) * b₁
    projection (concat H₁ H₂) c = (semiSpace a₃ b₃).solutions := by
  extract_lets
  rw [projection_concat_comm]
  apply proj_concat_semiSpace_nonorthogonal_neg_pos <;> assumption

section computeProjection

variable (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽)

def computeProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) : LinearSystem 𝔽 n :=
  let N := {i | S.mat i ⬝ᵥ c < 0}
  let Z := {i | S.mat i ⬝ᵥ c = 0}
  let P := {i | S.mat i ⬝ᵥ c > 0}
  let R := Z ⊕ₗ (N ×ₗ P)
  let r := Fintype.card R
  let p : Fin r ≃o R := Fintype.orderIsoFinOfCardEq R rfl
  let D : Matrix (Fin r) (Fin n) 𝔽 := Matrix.of fun i ↦
    match p i with
    | .inl s => S.mat s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t
  let d : Fin r → 𝔽 := fun i ↦
    match p i with
    | .inl s => S.vec s
    | .inr (s, t) => (S.mat t ⬝ᵥ c) • S.vec s - (S.mat s ⬝ᵥ c) • S.vec t
  of D d

lemma mem_computeProjection {S : LinearSystem 𝔽 n} {c} {x}
  : x ∈ (computeProjection S c).solutions ↔ ∃ α : 𝔽, x + α • c ∈ S.solutions := by
  let A := S.mat
  let b := S.vec
  unfold computeProjection
  lift_lets
  extract_lets N Z P R p D d
  let Λ : Fin S.m → 𝔽 := fun i ↦ (b i - A i ⬝ᵥ x) / (A i ⬝ᵥ c)
  let L := (N.image Λ).max
  let U := (P.image Λ).min
  have lemma_0
    : x ∈ (of D d).solutions
    ↔ ∀ (i : Fin R.card), match (p i).1 with
    | .inl i => A i ⬝ᵥ x ≤ b i
    | .inr (s, t) => ((A t ⬝ᵥ c) • A s - (A s ⬝ᵥ c) • A t) ⬝ᵥ x ≤ (A t ⬝ᵥ c) • b s - (A s ⬝ᵥ c) • b t
    := by
    simp_rw [mem_solutions]
    show (∀ (i : Fin R.card), D i ⬝ᵥ x ≤ d i) ↔ _
    apply forall_congr'
    intro i
    rcases hi : (p i).1 with s | ⟨s, t⟩ <;> simp only
    . have : D i = A s := by simp_all [funext_iff, D]
      have : d i = b s := by simp_all only [d]
      simp_all only
    . have : D i = ((A t ⬝ᵥ c) • A s - (A s ⬝ᵥ c) • A t) := by simp_all [funext_iff, D]
      have : d i = (A t ⬝ᵥ c) • b s - (A s ⬝ᵥ c) • b t := by simp_all only [d]
      simp_all only
  have lemma_1 (h : x ∈ (of D d).solutions) (α : 𝔽) (hl : L ≤ α) (hu : α ≤ U)
    : x + α • c ∈ S.solutions := by
    rw [mem_solutions, Pi.le_def, mulVec_add, mulVec_smul]
    rw [lemma_0] at h
    intro i
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change A i ⬝ᵥ x + α * A i ⬝ᵥ c ≤ b i
    rcases lt_trichotomy (A i ⬝ᵥ c) 0 with neg | zero | pos
    . have mem_N : i ∈ N := mem_filter_univ.mpr neg
      have : N.Nonempty := ⟨_, mem_N⟩
      simp [L, this] at hl
      rw [add_comm, ←le_sub_iff_add_le, ←div_le_iff_of_neg neg]
      exact hl _ mem_N
    . rw [zero, mul_zero, add_zero]
      have : i ∈ Z := mem_filter_univ.mpr zero
      have : Sum.inl i ∈ R := by simp_all [R]
      apply p.apply_symm_apply _ ▸ h (p.symm ⟨_, this⟩)
    . have mem_P : i ∈ P := mem_filter_univ.mpr pos
      have : P.Nonempty := ⟨_, mem_P⟩
      simp [U, this] at hu
      rw [add_comm, ←le_sub_iff_add_le, ←le_div_iff₀ pos]
      exact hu _ mem_P
  have lemma_2 (α : 𝔽) (h : x + α • c ∈ S.solutions) : x ∈ (of D d).solutions := by
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
      simp_rw [Z, mem_filter_univ] at hs
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
      simp_rw [N, P, mem_filter_univ] at hs ht
      have : ((S.mat t ⬝ᵥ c) • S.mat s - (S.mat s ⬝ᵥ c) • S.mat t) ⬝ᵥ (α • c) = 0 := by
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
  constructor <;> intro h
  . suffices h' : ∃ α : 𝔽, L ≤ α ∧ α ≤ U by
      obtain ⟨α, hl, hu⟩ := h'
      exact ⟨_, lemma_1 h α hl hu⟩
    match hL : L, hU : U with
    | ⊥, ⊤ => exact ⟨0, bot_le, le_top⟩
    | ⊥, .some u => exact ⟨u, bot_le, le_rfl⟩
    | .some l, ⊤ => exact ⟨l, le_rfl, le_top⟩
    | .some l, .some u =>
      have : l ≤ u := by
        unfold_let L U at hL hU
        suffices ∀ x ∈ N.image Λ, ∀ y ∈ P.image Λ, x ≤ y from
          this _ (Finset.mem_of_max hL) _ (Finset.mem_of_min hU)
        intro _ x_mem _ y_mem
        simp_rw [mem_image] at x_mem y_mem
        obtain ⟨i, mem_N, hi⟩ := x_mem
        obtain ⟨j, mem_P, hj⟩ := y_mem
        have : .inr (i, j) ∈ R := by
          apply mem_union_right
          apply mem_image_of_mem
          rw [mem_product]
          constructor <;> assumption
        let r : Fin R.card := p.symm ⟨_, this⟩
        replace := lemma_0.mp h r
        simp_rw [N, P, mem_filter, mem_univ, true_and] at mem_N mem_P
        subst hi hj
        simp_rw [r, OrderIso.apply_symm_apply, sub_dotProduct, smul_dotProduct, smul_eq_mul] at this
        simp_rw [Λ, div_le_iff_of_neg mem_N, mul_comm, ←mul_div_assoc, div_le_iff₀ mem_P, sub_mul,
          mul_sub, sub_le_iff_le_add, sub_add_comm, ←sub_le_iff_le_add]
        conv =>
          rw [←neg_le_neg_iff]
          simp only [neg_sub]
          congr <;> rw [mul_comm]
        exact this
      exists l
      simp [this]
  . obtain ⟨α, h⟩ := h
    apply lemma_2
    assumption

-- @[simp] theorem computeProjection_empty {c : Fin n → 𝔽}
--   : computeProjection LinearSystem.empty c = LinearSystem.empty := by
--   unfold computeProjection
--   lift_lets
--   extract_lets _ _ _ R _ D d
--   suffices R.card = 0 by
--     simp_rw [this] at D d
--     simp only [eq_empty_iff, this]
--   rw [card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
--   simp only [empty, IsEmpty.forall_iff]

-- @[simp] theorem computeProjection_cons_ortho
--   {a : Fin n → 𝔽} {b : 𝔽} {p : LinearSystem 𝔽 n} {c : Fin n → 𝔽}
--   (h : a ⬝ᵥ c = 0)
--   : computeProjection (cons a b p) c = cons a b (computeProjection p c) := by
--   rw [computeProjection]
--   lift_lets
--   extract_lets N Z P R p D d
--   suffices R.card = 0 by
--     simp_rw [this] at D d
--     simp only [eq_empty_iff, this]
--   rw [card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
--   simp only [empty, IsEmpty.forall_iff]

lemma solutions_computeProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽)
  : (computeProjection S c).solutions = { x | ∃ α : 𝔽, x + α • c ∈ S.solutions } := by
  unfold computeProjection
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

end computeProjection

end LinearSystem

namespace Polyhedron
open Matrix LinearSystem

-- def projection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) := { x | ∃ α : 𝔽, x + α • c ∈ P }

-- theorem projection_neg (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : P.projection (-c) = P.projection c := by
--   simp only [projection, Set.ext_iff, Set.mem_setOf]
--   intro x
--   constructor
--   all_goals (
--     intro h
--     obtain ⟨α, h⟩ := h
--     exists -α
--     simp_all
--   )

-- @[simp] lemma mem_projection {P : Polyhedron 𝔽 n}
--   : x ∈ P.projection c ↔ ∃ α : 𝔽, x + α • c ∈ P := Set.mem_setOf

-- @[simp]
-- lemma projection_semiSpace_orthogonal (a : Fin n → 𝔽) (b : 𝔽) (c : Fin n → 𝔽) (h : a ⬝ᵥ c = 0)
--   : projection (semiSpace a b) c = (semiSpace a b).toSet := by
--   simp_rw [projection, semiSpace_toSet, mem_semiSpace, Set.ext_iff, Set.mem_setOf]
--   intro x
--   constructor
--   . intro ⟨_, h'⟩
--     simp_rw [dotProduct_add, dotProduct_smul, h, smul_zero, add_zero] at h'
--     assumption
--   . intro h
--     exists 0
--     simp [h]

-- @[simp]
-- lemma projection_semiSpace_nonorthogonal (a : Fin n → 𝔽) (b : 𝔽) (c : Fin n → 𝔽) (h : a ⬝ᵥ c ≠ 0)
--   : projection (semiSpace a b) c = Set.univ := by
--   simp_rw [projection, mem_semiSpace, Set.eq_univ_iff_forall, Set.mem_setOf]
--   intro x
--   simp_rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
--   exists (b - a ⬝ᵥ x)/(a ⬝ᵥ c)
--   simp_rw [div_mul_cancel₀ _ h, add_sub_cancel]
--   rfl

-- @[simp] theorem proj_inter_semiSpace_orthogonal
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c = 0)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     projection (H₁ ∩ H₂) c = H₁ ∩ H₂ := by
--   ext x
--   simp_all

-- @[simp] theorem proj_inter_semiSpace_orthogonal_left
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c ≠ 0)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     projection (H₁ ∩ H₂) c = H₁ := by
--   ext x
--   simp_rw [mem_projection, mem_inter, ←mem_def, mem_semiSpace, dotProduct_add, dotProduct_smul, h₁,
--     smul_zero, add_zero, exists_and_left, and_iff_left_iff_imp]
--   intro
--   exists (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
--   simp_rw [smul_eq_mul, div_mul_cancel₀ _ h₂, add_sub_cancel]
--   rfl

-- @[simp] theorem proj_inter_semiSpace_orthogonal_right
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : a₁ ⬝ᵥ c ≠ 0) (h₂ : a₂ ⬝ᵥ c = 0)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     projection (H₁ ∩ H₂) c = H₂ := by
--   unfold_let
--   rw [inter_comm]
--   apply proj_inter_semiSpace_orthogonal_left _ _ _ _ _ h₂ h₁

-- @[simp] theorem proj_inter_semiSpace_nonorthogonal_pos
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : 0 < a₂ ⬝ᵥ c)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     projection (H₁ ∩ H₂) c = Set.univ := by
--   rw [Set.eq_univ_iff_forall]
--   intro x
--   simp_rw [mem_projection, mem_inter, mem_semiSpace, dotProduct_add, dotProduct_smul, smul_eq_mul]
--   let l := (b₁ - a₁ ⬝ᵥ x)/(a₁ ⬝ᵥ c)
--   let r := (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
--   exists min l r
--   constructor
--   . calc
--       _ ≤ a₁ ⬝ᵥ x + l * a₁ ⬝ᵥ c := by
--         rw [add_le_add_iff_left, mul_le_mul_right h₁]
--         apply min_le_left
--       _ = _ := by
--         simp_rw [l, div_mul_cancel₀ _ h₁.ne.symm, add_sub_cancel]
--   . calc
--       _ ≤ a₂ ⬝ᵥ x + r * a₂ ⬝ᵥ c := by
--         rw [add_le_add_iff_left, mul_le_mul_right h₂]
--         apply min_le_right
--       _ = _ := by
--         simp_rw [r, div_mul_cancel₀ _ h₂.ne.symm, add_sub_cancel]

-- @[simp] theorem proj_inter_semiSpace_nonorthogonal_neg
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : a₂ ⬝ᵥ c < 0)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     projection (H₁ ∩ H₂) c = Set.univ := by
--   extract_lets
--   rw [←projection_neg]
--   apply proj_inter_semiSpace_nonorthogonal_pos <;> simp_all

-- @[simp] theorem proj_inter_semiSpace_nonorthogonal_neg_pos
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : 0 < a₂ ⬝ᵥ c)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     let a₃ := (a₂ ⬝ᵥ c) • a₁ - (a₁ ⬝ᵥ c) • a₂
--     let b₃ := (a₂ ⬝ᵥ c) * b₁ - (a₁ ⬝ᵥ c) * b₂
--     projection (H₁ ∩ H₂) c = semiSpace a₃ b₃ := by
--   ext x
--   simp_rw [←mem_def, mem_projection, mem_inter, mem_semiSpace]
--   constructor
--   . intro ⟨α, h₁', h₂'⟩
--     simp_rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, sub_le_sub_iff, add_comm,
--       ←sub_le_sub_iff, ←mul_sub]
--     rw [dotProduct_add, dotProduct_smul, ←le_sub_iff_add_le', smul_eq_mul] at h₁' h₂'
--     rw [←div_le_iff_of_neg' h₁]
--     calc
--       _ ≤ α * a₂ ⬝ᵥ c := by
--         rw [mul_comm, mul_div_assoc, ←div_le_iff_of_neg]
--         . calc
--           _ ≤ α * a₁ ⬝ᵥ c := by
--             rw [div_div_eq_mul_div, mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ h₂.ne.symm]
--           _ ≤ _ := h₁'
--         . simp [div_neg_iff, h₁, h₂]
--       _ ≤ _ := h₂'
--   . intro h
--     simp_rw [sub_dotProduct, smul_dotProduct, sub_le_sub_iff, add_comm, ←sub_le_sub_iff,
--       smul_eq_mul, ←mul_sub, mul_comm, ←div_le_iff₀ h₂, mul_div_assoc, ←div_le_iff_of_neg' h₁] at h
--     exists (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
--     simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
--     constructor
--     . apply add_le_of_le_sub_left
--       rw [←div_le_iff_of_neg h₁]
--       assumption
--     . simp [div_mul_cancel₀ _ h₂.ne.symm]

-- @[simp]
-- theorem proj_inter_semiSpace_nonorthogonal_pos_neg
--   (a₁ a₂ : Fin n → 𝔽) (b₁ b₂ : 𝔽) (c : Fin n → 𝔽)
--   (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : a₂ ⬝ᵥ c < 0)
--   : let H₁ := semiSpace a₁ b₁
--     let H₂ := semiSpace a₂ b₂
--     let a₃ := (a₁ ⬝ᵥ c) • a₂ - (a₂ ⬝ᵥ c) • a₁
--     let b₃ := (a₁ ⬝ᵥ c) * b₂ - (a₂ ⬝ᵥ c) * b₁
--     projection (H₁ ∩ H₂) c = semiSpace a₃ b₃ := by
--   extract_lets
--   rw [inter_comm]
--   apply proj_inter_semiSpace_nonorthogonal_neg_pos
--   . exact h₂
--   . exact h₁

def computeProjection (p : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  Quotient.liftOn p
    (fun S ↦ computeProjection S c)
    (fun a b h ↦ toSet_inj.mp $
      (solutions_computeProjection a _).trans (h ▸ solutions_computeProjection b _).symm)

-- @[simp]
-- theorem mem_computeProjection {p : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
--   : x ∈ p.computeProjection c ↔ ∃ α : 𝔽, x + α • c ∈ p := by
--   induction p using Quotient.ind
--   unfold computeProjection
--   simp_rw [Quotient.lift_mk, mem_ofLinearSystem, solutions_computeProjection, Set.mem_setOf]
--   rfl

-- def projection (S H : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
--   H ∩ S.computeProjection c

-- @[simp] theorem mem_projection {S H : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
--   : x ∈ S.projection H c ↔ x ∈ H ∧ ∃ α : 𝔽, x + α • c ∈ S := by simp [projection]

-- @[simp] theorem subset_computeProjection {S : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
--   : S ⊆ S.computeProjection c := by
--   intro x
--   rw [mem_computeProjection]
--   intro x_mem_S
--   exists 0
--   rw [zero_smul, add_zero]
--   assumption

-- theorem projection_self (p : Polyhedron 𝔽 n) (c) : p.projection p c = p := by
--   apply subset_antisymm
--   . apply inter_subset_left
--   . apply subset_inter
--     . apply subset_refl
--     . apply subset_computeProjection

-- def fourierMotzkin (p : Polyhedron 𝔽 n) (j : Fin n) := p.projection !P{x_[j] = 0} x_[j]

-- theorem mem_fourierMotzkin (p : Polyhedron 𝔽 n) (j : Fin n) :
--   x ∈ p.fourierMotzkin j ↔ x j = 0 ∧ ∃ (α : 𝔽), x + Pi.single j α ∈ p := by
--   simp_rw [
--     fourierMotzkin, mem_projection, mem_ofConstraints,
--     List.mem_singleton, forall_eq, LinearConstraint.valid,
--     single_dotProduct, one_mul, and_congr_right_iff,
--     ←Pi.single_smul, smul_eq_mul, mul_one, implies_true
--   ]

-- theorem coord_zero_of_mem_fourierMotzkin {p : Polyhedron 𝔽 n} {j : Fin n} {x : Fin n → 𝔽}
--   (h : x ∈ p.fourierMotzkin j) : x j = 0 := by
--   rw [mem_fourierMotzkin] at h
--   exact h.1

-- @[simp] theorem computeProjection_eq_empty_iff (p : Polyhedron 𝔽 n) (c)
--   : p.computeProjection c = ∅ ↔ p = ∅ := by
--   constructor <;> intro h
--   . have := projection_self p c
--     simp_rw [Polyhedron.ext_iff, mem_projection] at this
--     simp_rw [eq_empty_iff, mem_computeProjection] at h ⊢
--     simp_all
--   . simp_rw [eq_empty_iff, mem_computeProjection]
--     simp_all [not_mem_empty]

-- def recElimDimensions (p : Polyhedron 𝔽 n) {k : ℕ} (h : k ≤ n) :=
--   match k with
--   | 0 => p
--   | k + 1 => (p.recElimDimensions $ le_of_add_le_left h).computeProjection x_[⟨k, h⟩]

-- @[simp] theorem recElimDimensions_eq_empty_iff (p : Polyhedron 𝔽 n) {k : ℕ} (hk : k ≤ n)
--   : p.recElimDimensions hk = ∅ ↔ p = ∅ := by
--   unfold recElimDimensions
--   split
--   . rfl
--   . rw [computeProjection_eq_empty_iff]
--     apply p.recElimDimensions_eq_empty_iff

-- theorem recElimDimensions_all_empty_or_univ (p : Polyhedron 𝔽 n) {k : ℕ}
--   : let p' := p.recElimDimensions (le_refl _); p' = ∅ ∨ p' = ⊤ := by
--   unfold recElimDimensions
--   split
--   . by_cases finZeroElim ∈ p <;> simp_all [Polyhedron.ext_iff, not_mem_empty, mem_univ]
--   . simp only [Nat.succ_eq_add_one, computeProjection_eq_empty_iff, recElimDimensions_eq_empty_iff]
--     by_cases p = ∅
--     . left; assumption
--     . right
--       simp_rw [Polyhedron.ext_iff, mem_computeProjection, mem_univ, iff_true]
--       intro x
--       sorry

end Polyhedron
