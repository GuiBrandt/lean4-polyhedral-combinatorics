import PolyhedralCombinatorics.Polyhedron.Basic

variable {𝔽} [lof : LinearOrderedField 𝔽] {n : ℕ}

namespace LinearSystem
open Matrix Finset

def projection (P : LinearSystem 𝔽 n) (c : Fin n → 𝔽) := { x | ∃ α : 𝔽, x + α • c ∈ P.solutions }

theorem projection_neg (P : LinearSystem 𝔽 n) (c : Fin n → 𝔽)
  : P.projection (-c) = P.projection c := by
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

end LinearSystem


namespace Polyhedron
open Matrix LinearSystem

def projection (P : Polyhedron 𝔽 n) (c : Fin n → 𝔽) := {x | ∃ α : 𝔽, x + α • c ∈ P}

@[simp] lemma mem_projection {P : Polyhedron 𝔽 n}
  : x ∈ P.projection c ↔ ∃ α : 𝔽, x + α • c ∈ P := Set.mem_setOf

end Polyhedron
