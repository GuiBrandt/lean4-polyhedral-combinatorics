import PolyhedralCombinatorics.Projection.FourierMotzkin
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace LinearSystem.Duality
open Polyhedron Matrix

variable {𝔽 : Type*} [LinearOrderedField 𝔽] {m n : ℕ}

theorem farkas_lemma {A : Matrix (Fin m) (Fin n) 𝔽} {b : Fin m → 𝔽}
  : (∃ x, x ∈ P(A, b)) ↔ ∀ y, y ≥ 0 → y ᵥ* A = 0 → y ⬝ᵥ b ≥ 0 := by
  constructor <;> intro h
  . intro y y_nonneg hy
    obtain ⟨x, hx⟩ := h
    rw [mem_ofLinearSystem_of] at hx
    have := dotProduct_le_dotProduct_of_nonneg_left hx y_nonneg
    rw [dotProduct_mulVec, hy, zero_dotProduct] at this
    assumption
  . by_contra hc
    simp_rw [not_exists, ←Polyhedron.eq_empty_iff] at hc
    sorry
