import PolyhedralCombinatorics.Polyhedron.Basic
import PolyhedralCombinatorics.Polyhedron.Notation

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sum.Order

import Mathlib.Order.WellFoundedSet

import Mathlib.Tactic.LiftLets

import Utils.IsEmpty

variable {𝔽} [lof : LinearOrderedField 𝔽] {n : ℕ}

lemma Finset.mem_filter_univ {α} [Fintype α] {x : α} {p : α → Prop} [DecidablePred p]
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
  : projection (P ++ Q) c = projection (Q ++ P) c := by
  unfold projection
  simp_rw [concat_solutions, Set.inter_comm]

@[simp low] lemma mem_projection {P : LinearSystem 𝔽 n}
  : x ∈ P.projection c ↔ ∃ α : 𝔽, x + α • c ∈ P.solutions := Set.mem_setOf

@[simp]
lemma proj_semiSpace_orthogonal {a : Fin n → 𝔽} {b : 𝔽} {c : Fin n → 𝔽} (h : a ⬝ᵥ c = 0)
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
lemma proj_semiSpace_nonorthogonal {a : Fin n → 𝔽} {b : 𝔽} {c : Fin n → 𝔽} (h : a ⬝ᵥ c ≠ 0)
  : projection (semiSpace a b) c = Set.univ := by
  simp_rw [projection, mem_semiSpace, Set.eq_univ_iff_forall, Set.mem_setOf]
  intro x
  simp_rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  exists (b - a ⬝ᵥ x)/(a ⬝ᵥ c)
  simp_rw [div_mul_cancel₀ _ h, add_sub_cancel]
  rfl

@[simp] theorem proj_concat_semiSpace_orthogonal
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c = 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (H₁ ++ H₂) c = (H₁ ++ H₂).solutions := by
  ext x
  simp_rw [projection, mem_concat, Set.mem_setOf, mem_semiSpace, dotProduct_add, dotProduct_smul,
    h₁, h₂, smul_zero, add_zero, exists_const]

@[simp] theorem proj_concat_semiSpace_orthogonal_left
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : a₁ ⬝ᵥ c = 0) (h₂ : a₂ ⬝ᵥ c ≠ 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (H₁ ++ H₂) c = H₁.solutions := by
  ext x
  simp_rw [mem_projection, concat_solutions, Set.mem_inter_iff, mem_semiSpace, dotProduct_add,
    dotProduct_smul, h₁, smul_zero, add_zero, exists_and_left, and_iff_left_iff_imp]
  intro
  exists (b₂ - a₂ ⬝ᵥ x)/(a₂ ⬝ᵥ c)
  simp_rw [smul_eq_mul, div_mul_cancel₀ _ h₂, add_sub_cancel]
  rfl

@[simp] theorem proj_concat_semiSpace_orthogonal_right
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : a₁ ⬝ᵥ c ≠ 0) (h₂ : a₂ ⬝ᵥ c = 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (H₁ ++ H₂) c = H₂.solutions := by
  extract_lets H₁ H₂
  rw [projection_concat_comm]
  exact proj_concat_semiSpace_orthogonal_left (b₁ := b₂) (b₂ := b₁) h₂ h₁

@[simp] theorem proj_concat_semiSpace_nonorthogonal_pos
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : 0 < a₂ ⬝ᵥ c)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (H₁ ++ H₂) c = Set.univ := by
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
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : a₂ ⬝ᵥ c < 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    projection (H₁ ++ H₂) c = Set.univ := by
  extract_lets
  rw [←projection_neg]
  apply proj_concat_semiSpace_nonorthogonal_pos <;> simp_all

@[simp] theorem proj_concat_semiSpace_nonorthogonal_neg_pos
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : a₁ ⬝ᵥ c < 0) (h₂ : 0 < a₂ ⬝ᵥ c)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    let a₃ := (a₂ ⬝ᵥ c) • a₁ - (a₁ ⬝ᵥ c) • a₂
    let b₃ := (a₂ ⬝ᵥ c) * b₁ - (a₁ ⬝ᵥ c) * b₂
    projection (H₁ ++ H₂) c = (semiSpace a₃ b₃).solutions := by
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
  {a₁ a₂ : Fin n → 𝔽} {b₁ b₂ : 𝔽} {c : Fin n → 𝔽}
  (h₁ : 0 < a₁ ⬝ᵥ c) (h₂ : a₂ ⬝ᵥ c < 0)
  : let H₁ := semiSpace a₁ b₁
    let H₂ := semiSpace a₂ b₂
    let a₃ := (a₁ ⬝ᵥ c) • a₂ - (a₂ ⬝ᵥ c) • a₁
    let b₃ := (a₁ ⬝ᵥ c) * b₂ - (a₂ ⬝ᵥ c) * b₁
    projection (H₁ ++ H₂) c = (semiSpace a₃ b₃).solutions := by
  extract_lets
  rw [projection_concat_comm]
  apply proj_concat_semiSpace_nonorthogonal_neg_pos <;> assumption

lemma projection_inter_pairs (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) {x}
  : x ∈ S.projection c ↔ ∀ i j, x ∈ (S.ith_semiSpace i ++ S.ith_semiSpace j).projection c := by
  constructor
  . rw [mem_projection]
    intro ⟨α, h⟩ i j
    exists α
    simp_rw [concat_solutions, Set.mem_inter_iff, mem_semiSpace]
    exact ⟨h i, h j⟩
  . intro h
    simp_rw [mem_projection] at h ⊢
    let N : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c < 0}
    let Z : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c = 0}
    let P : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c > 0}
    let Λ : Fin S.m → 𝔽 := fun i ↦ (S.vec i - S.mat i ⬝ᵥ x) / (S.mat i ⬝ᵥ c)
    let L := (N.image Λ).max
    let U := (P.image Λ).min
    have ⟨α, hl, hu⟩ : ∃ α : 𝔽, L ≤ α ∧ α ≤ U := by
      match hL : L, hU : U with
      | ⊥, ⊤ => exact ⟨0, bot_le, le_top⟩
      | ⊥, .some u => exact ⟨u, bot_le, le_rfl⟩
      | .some l, ⊤ => exact ⟨l, le_rfl, le_top⟩
      | .some l, .some u =>
        have hN : N.Nonempty := Finset.image_nonempty.mp ⟨l, Finset.mem_of_max hL⟩
        have hP : P.Nonempty := Finset.image_nonempty.mp ⟨u, Finset.mem_of_min hU⟩
        unfold_let L U at hL hU
        let ⟨i, hi₁, hi₂⟩ := Finset.mem_image.mp $ Finset.mem_of_max hL
        let ⟨j, hj₁, hj₂⟩ := Finset.mem_image.mp $ Finset.mem_of_min hU
        simp_rw [N, P, mem_filter_univ] at hi₁ hj₁
        subst l u
        replace ⟨α, h⟩ := h i j
        simp_rw [mem_concat, mem_semiSpace] at h
        simp only [WithBot.coe_le_coe, WithTop.coe_le_coe]
        exists α
        constructor <;> by_contra hc <;> rw [not_le] at hc
        . replace h := h.1
          simp_rw [dotProduct_add, dotProduct_smul] at h
          have : S.mat i ⬝ᵥ x + α • (S.mat i ⬝ᵥ c) > S.vec i := calc
            _ > _ + Λ i • _ := by
              apply add_lt_add_left
              exact mul_lt_mul_of_neg_right hc hi₁
            _ = _ := by simp_rw [Λ, smul_eq_mul, div_mul_cancel₀ _ hi₁.ne, add_sub_cancel]
          linarith
        . replace h := h.2
          simp_rw [dotProduct_add, dotProduct_smul] at h
          have : S.mat j ⬝ᵥ x + α • (S.mat j ⬝ᵥ c) > S.vec j := calc
            _ > _ + Λ j • _ := by
              apply add_lt_add_left
              exact mul_lt_mul_of_pos_right hc hj₁
            _ = _ := by simp_rw [Λ, smul_eq_mul, div_mul_cancel₀ _ hj₁.ne', add_sub_cancel]
          linarith
    exists α
    rw [mem_solutions, Pi.le_def, mulVec_add, mulVec_smul]
    intro i
    rw [Pi.add_apply, Pi.smul_apply]
    change S.mat i ⬝ᵥ x + α * S.mat i ⬝ᵥ c ≤ S.vec i
    rcases lt_trichotomy (S.mat i ⬝ᵥ c) 0 with neg | zero | pos
    . have mem_N : i ∈ N := mem_filter_univ.mpr neg
      have : N.Nonempty := ⟨_, mem_N⟩
      simp only [Finset.max_le_iff, mem_image, WithBot.coe_le_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, L] at hl
      rw [add_comm, ←le_sub_iff_add_le, ←div_le_iff_of_neg neg]
      exact hl _ mem_N
    . rw [zero, mul_zero, add_zero]
      have : i ∈ Z := mem_filter_univ.mpr zero
      have ⟨α', hα'⟩ := h i i
      rw [mem_concat, and_self, mem_semiSpace, dotProduct_add, dotProduct_smul, zero, smul_zero,
        add_zero] at hα'
      assumption
    . have mem_P : i ∈ P := mem_filter_univ.mpr pos
      have : P.Nonempty := ⟨_, mem_P⟩
      simp only [Finset.le_min_iff, mem_image, WithTop.coe_le_coe, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, U] at hu
      rw [add_comm, ←le_sub_iff_add_le, ←le_div_iff₀ pos]
      exact hu _ mem_P

lemma projection_inter_pairs' (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) {x}
  : x ∈ S.projection c ↔
    (∀ i, S.mat i ⬝ᵥ c = 0 → x ∈ (S.ith_semiSpace i).solutions)
    ∧ (∀ i j, S.mat i ⬝ᵥ c < 0 → S.mat j ⬝ᵥ c > 0 →
        x ∈ (S.ith_semiSpace i ++ S.ith_semiSpace j).projection c) := by
    apply (S.projection_inter_pairs c).trans
    constructor
    . intro h
      constructor
      . intro i hi
        have := h i i
        rw [proj_concat_semiSpace_orthogonal hi hi, mem_concat, and_self] at this
        exact this
      . intro i j _ _
        apply h
    . intro ⟨hz, hnp⟩ i j
      rcases lt_trichotomy (S.mat i ⬝ᵥ c) 0 with neg₁ | zero₁ | pos₁
      <;> rcases lt_trichotomy (S.mat j ⬝ᵥ c) 0 with neg₂ | zero₂ | pos₂
      . rw [proj_concat_semiSpace_nonorthogonal_neg]
        repeat trivial
      . rw [proj_concat_semiSpace_orthogonal_right neg₁.ne zero₂]
        apply hz j zero₂
      . exact hnp i j neg₁ pos₂
      . rw [proj_concat_semiSpace_orthogonal_left zero₁ neg₂.ne]
        apply hz i zero₁
      . rw [proj_concat_semiSpace_orthogonal zero₁ zero₂, mem_concat]
        exact ⟨hz i zero₁, hz j zero₂⟩
      . rw [proj_concat_semiSpace_orthogonal_left zero₁ pos₂.ne']
        apply hz i zero₁
      . rw [projection_concat_comm]
        exact hnp j i neg₂ pos₁
      . rw [proj_concat_semiSpace_orthogonal_right pos₁.ne' zero₂]
        apply hz j zero₂
      . rw [proj_concat_semiSpace_nonorthogonal_pos]
        repeat trivial

def computeProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) : LinearSystem 𝔽 n :=
  let N : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c < 0}
  let Z : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c = 0}
  let P : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c > 0}
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

@[simp] theorem mem_computeProjection {S : LinearSystem 𝔽 n} {c} {x}
  : x ∈ (computeProjection S c).solutions ↔ x ∈ S.projection c := by
  let A := S.mat
  let b := S.vec
  unfold computeProjection
  lift_lets
  extract_lets _ _ _ _ r p D d
  rw [projection_inter_pairs']
  show (∀ (i : Fin r), D i ⬝ᵥ x ≤ d i) ↔ _
  constructor
  . intro h
    constructor
    . intro i hi
      rw [mem_semiSpace]
      have := h $ p.symm $ Sum.inl ⟨i, mem_filter_univ.mpr hi⟩
      simp only [D, d, dotProduct, Matrix.of_apply, OrderIso.apply_symm_apply] at this
      exact this
    . intro i j hi hj
      have := h $ p.symm $ Sum.inr ⟨⟨i, mem_filter_univ.mpr hi⟩, ⟨j, mem_filter_univ.mpr hj⟩⟩
      simp only [D, d, dotProduct, Matrix.of_apply, OrderIso.apply_symm_apply] at this
      rw [proj_concat_semiSpace_nonorthogonal_neg_pos hi hj, mem_semiSpace]
      exact this
  . intro ⟨hz, hnp⟩ i
    rcases hi : p i with s | ⟨s, t⟩
    . have hD : D i = A s := by simp only [D, funext_iff, of_apply, hi, implies_true]
      have hd : d i = b s := by simp only [d, hi]
      have hs := Finset.mem_filter_univ.mp s.property
      replace := hz s hs
      rw [mem_semiSpace] at this
      rw [hD, hd]
      exact this
    . have hD : D i = ((A t ⬝ᵥ c) • A s - (A s ⬝ᵥ c) • A t) := by simp_all only [D, funext_iff, of_apply, implies_true]
      have hd : d i = (A t ⬝ᵥ c) • b s - (A s ⬝ᵥ c) • b t := by simp_all only [d]
      have hs := mem_filter_univ.mp s.property
      have ht := mem_filter_univ.mp t.property
      replace := hnp s t hs ht
      rw [proj_concat_semiSpace_nonorthogonal_neg_pos hs ht, mem_semiSpace] at this
      rw [hD, hd]
      exact this

@[simp] lemma solutions_computeProjection (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽)
  : (computeProjection S c).solutions = S.projection c := by
  simp_rw [Set.ext_iff, mem_projection]
  apply mem_computeProjection

end LinearSystem

namespace Polyhedron
open Matrix LinearSystem

def projection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) := {x | ∃ α : 𝔽, x + α • c ∈ P}

@[simp] lemma mem_projection {P : Polyhedron 𝔽 n}
  : x ∈ P.projection c ↔ ∃ α : 𝔽, x + α • c ∈ P := Set.mem_setOf

def computeProjection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  Quotient.liftOn P (fun S ↦ S.computeProjection c) fun a b h ↦ by
    apply toSet_inj.mp
    simp_rw [toSet_ofLinearSystem, solutions_computeProjection, LinearSystem.projection]
    rw [h]

@[simp]
theorem mem_computeProjection {P : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : x ∈ P.computeProjection c ↔ ∃ α : 𝔽, x + α • c ∈ P := by
  induction P using Quotient.ind
  unfold computeProjection
  simp_rw [Quotient.lift_mk, mem_ofLinearSystem, solutions_computeProjection]
  rfl

@[simp] theorem subset_computeProjection {P : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : P ⊆ P.computeProjection c := by
  intro x
  rw [mem_computeProjection]
  intro x_mem_S
  exists 0
  rw [zero_smul, add_zero]
  assumption

theorem projection_self (P : Polyhedron 𝔽 n) (c) : P ∩ P.computeProjection c = P := by
  apply subset_antisymm
  . apply inter_subset_left
  . apply subset_inter
    . apply subset_refl
    . apply subset_computeProjection

def fourierMotzkin (P : Polyhedron 𝔽 n) (j : Fin n) :=
  !P{x_[j] = 0} ∩ P.computeProjection x_[j]

theorem mem_fourierMotzkin (P : Polyhedron 𝔽 n) (j : Fin n) :
  x ∈ P.fourierMotzkin j ↔ x j = 0 ∧ ∃ (α : 𝔽), x + Pi.single j α ∈ P := by
  simp_rw [
    fourierMotzkin, mem_inter, mem_computeProjection, mem_ofConstraints,
    List.mem_singleton, forall_eq, LinearConstraint.valid,
    single_dotProduct, one_mul, and_congr_right_iff,
    ←Pi.single_smul, smul_eq_mul, mul_one, implies_true
  ]

@[simp] theorem computeProjection_eq_empty_iff (P : Polyhedron 𝔽 n) (c)
  : P.computeProjection c = ∅ ↔ P = ∅ := by
  constructor <;> intro h
  . have := projection_self P c
    simp_rw [Polyhedron.ext_iff, mem_inter, mem_computeProjection] at this
    simp_rw [eq_empty_iff, mem_computeProjection] at h ⊢
    simp_all
  . simp_rw [eq_empty_iff, mem_computeProjection]
    simp_all [not_mem_empty]

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
