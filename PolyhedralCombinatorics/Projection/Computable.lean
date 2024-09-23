import PolyhedralCombinatorics.Projection.SemiSpace
import PolyhedralCombinatorics.LinearSystem.Notation

import Mathlib.Data.Matrix.Reflection
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Sum.Order

import Mathlib.Tactic.LiftLets

import Utils.IsEmpty
import Utils.Finset

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

namespace LinearSystem
open Matrix Finset

def projectionMatrix (S : LinearSystem 𝔽 n) (c : Fin n → 𝔽) :=
  let N : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c < 0}
  let Z : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c = 0}
  let P : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c > 0}
  let R := Z ⊕ₗ (N ×ₗ P)
  let r := Fintype.card R
  let p : Fin r ≃o R := Fintype.orderIsoFinOfCardEq R rfl
  let U : Matrix (Fin _) (Fin S.m) 𝔽 := Matrix.of fun i ↦
      match p i with
      | .inl s => Pi.single ↑s 1
      | .inr (s, t) => Pi.single ↑s (S.mat t ⬝ᵥ c) - Pi.single ↑t (S.mat s ⬝ᵥ c)
  U

abbrev transform (S : LinearSystem 𝔽 n) {r : ℕ} (T : Matrix (Fin r) (Fin S.m) 𝔽)
  : LinearSystem 𝔽 n := of (T * S.mat) (T *ᵥ S.vec)

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

theorem projectionMatrix_positive {S : LinearSystem 𝔽 n} {c : Fin n → 𝔽}
  : let U := S.projectionMatrix c
    ∀ i, U i ≥ 0 := by
  unfold projectionMatrix
  lift_lets
  extract_lets _ _ _ _ r p U
  simp_rw [U, Pi.le_def, of_apply, Pi.zero_apply]
  intro i j
  rcases p i with s | ⟨s, t⟩ <;> simp only
  . rw [Pi.single_apply]
    split <;> simp only [zero_le_one, le_refl]
  . simp_rw [Pi.sub_apply, Pi.single_apply]
    have hs := (mem_filter_univ.mp s.prop).le
    have ht := (mem_filter_univ.mp t.prop).le
    split <;> split <;> simp_all

theorem computeProjection_eq_transform {S : LinearSystem 𝔽 n} {c : Fin n → 𝔽}
  : S.computeProjection c = S.transform (S.projectionMatrix c) := by
  unfold computeProjection transform
  lift_lets
  extract_lets _ _ _ _ r p D d
  simp_rw [eq_iff_of_m_eq]
  constructor
  funext (i : Fin r) (j : Fin n)
  simp_rw [mul_apply', projectionMatrix, D, of_apply]
  rotate_left
  funext (i : Fin r)
  simp_rw [projectionMatrix, d, mulVec, of_apply]
  all_goals (
    rcases p i with s | ⟨s, t⟩ <;> simp only
    . simp only [single_dotProduct, one_mul]
    . simp_rw [sub_dotProduct, single_dotProduct]
      rfl
  )

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

theorem computeProjection_mat_ortho {S : LinearSystem 𝔽 n} {c : Fin n → 𝔽}
  : (computeProjection S c).mat *ᵥ c = 0 := by
  unfold computeProjection
  lift_lets
  extract_lets _ Z _ _ r p D _
  funext i
  simp_rw [mulVec, Pi.zero_apply, D, Matrix.of_apply]
  eta_reduce
  split
  . rename_i s _
    have := mem_filter_univ.mp s.property
    assumption
  . simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [mul_comm, sub_self]

def projectionMatrix' (S : LinearSystem 𝔽 n) {m : ℕ} (c : Matrix (Fin (m + 1)) (Fin n) 𝔽)
  : let N : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c 0 < 0}
    let Z : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c 0 = 0}
    let P : Finset (Fin S.m) := {i | S.mat i ⬝ᵥ c 0 > 0}
    let R := Z ⊕ₗ (N ×ₗ P)
    let r := Fintype.card R
    Matrix (Fin r) (Fin S.m) 𝔽 :=
  match m with
  | 0 => S.projectionMatrix (c 0)
  | n + 1 =>
    let U := S.projectionMatrix (c 0)
    let U' := S.projectionMatrix' (vecTail c)
    U' * U

end LinearSystem

namespace Polyhedron

def computeProjection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) : Polyhedron 𝔽 n :=
  Quotient.liftOn P (fun S ↦ S.computeProjection c) fun a b h ↦ by
    apply toSet_inj.mp
    simp_rw [toSet_ofLinearSystem, LinearSystem.solutions_computeProjection, LinearSystem.projection]
    rw [h]

@[simp]
theorem mem_computeProjection {P : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : x ∈ P.computeProjection c ↔ ∃ α : 𝔽, x + α • c ∈ P := by
  induction P using Quotient.ind
  unfold computeProjection
  simp_rw [Quotient.lift_mk, mem_ofLinearSystem, LinearSystem.solutions_computeProjection]
  rfl

@[simp] theorem subset_computeProjection {P : Polyhedron 𝔽 n} {c : Fin n → 𝔽}
  : P ⊆ P.computeProjection c := by
  intro x
  rw [mem_computeProjection]
  intro x_mem_S
  exists 0
  rw [zero_smul, add_zero]
  assumption

theorem self_inter_computeProjection (P : Polyhedron 𝔽 n) (c) : P ∩ P.computeProjection c = P := by
  apply subset_antisymm
  . apply inter_subset_left
  . apply subset_inter
    . apply subset_refl
    . apply subset_computeProjection

@[simp] theorem computeProjection_eq_empty_iff (P : Polyhedron 𝔽 n) (c)
  : P.computeProjection c = ∅ ↔ P = ∅ := by
  constructor <;> intro h
  . have := self_inter_computeProjection P c
    simp_rw [Polyhedron.ext_iff, mem_inter, mem_computeProjection] at this
    simp_rw [eq_empty_iff, mem_computeProjection] at h ⊢
    simp_all
  . simp_rw [eq_empty_iff, mem_computeProjection]
    simp_all [not_mem_empty]

end Polyhedron
