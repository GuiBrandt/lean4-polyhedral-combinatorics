import PolyhedralCombinatorics.LinearSystem.LinearConstraints

import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.Normed.Group.Constructions -- Vector (Pi type) norm

variable (𝔽 : Type u₁) [LinearOrderedField 𝔽] (n : ℕ)

/-- `Polyhedron 𝔽 n` is the type of polyhedra in `𝔽^n`, where `𝔽` is a linear ordered field. -/
def Polyhedron := Quotient (LinearSystem.isSetoid 𝔽 n)

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽 n} [LinearOrderedField 𝔽] (p : Polyhedron 𝔽 n)

/-- Notation for the polyhedron `{ x ∈ 𝔽^n | A x ≤ b }` -/
@[coe] def ofLinearSystem : LinearSystem 𝔽 n → Polyhedron 𝔽 n := Quotient.mk _

instance : Coe (LinearSystem 𝔽 n) (Polyhedron 𝔽 n) := ⟨ofLinearSystem⟩

/-- The set of points in `p`. -/
@[coe] def toSet : Set (Fin n → 𝔽) := Quotient.lift solutions (fun _ _ ↦ id) p

instance instCoeSet : Coe (Polyhedron 𝔽 n) (Set (Fin n → 𝔽)) := ⟨toSet⟩

/-- Membership in a polyhedron. -/
abbrev Mem (x : Fin n → 𝔽) (p : Polyhedron 𝔽 n) := x ∈ p.toSet

instance instMembership : Membership (Fin n → 𝔽) (Polyhedron 𝔽 n) := ⟨Mem⟩

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

section Notation

end Notation
