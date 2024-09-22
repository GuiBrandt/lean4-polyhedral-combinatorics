import PolyhedralCombinatorics.Projection.FourierMotzkin

import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace LinearSystem
open Matrix

variable {𝔽 : Type*} [LinearOrderedField 𝔽] {m n : ℕ}

theorem farkas_lemma {S : LinearSystem 𝔽 n}
  : (∃ x, x ∈ S.solutions) ↔ ∀ y ≥ 0, y ᵥ* S.mat = 0 → y ⬝ᵥ S.vec ≥ 0 := by
  constructor <;> intro h
  . intro y y_nonneg hy
    obtain ⟨x, hx⟩ := h
    have := dotProduct_le_dotProduct_of_nonneg_left hx y_nonneg
    rw [dotProduct_mulVec, hy, zero_dotProduct] at this
    assumption
  . by_contra hc
    sorry
