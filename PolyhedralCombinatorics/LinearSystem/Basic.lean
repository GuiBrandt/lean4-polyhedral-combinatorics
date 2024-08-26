import PolyhedralCombinatorics.LinearSystem.Defs

namespace LinearSystem
open Matrix

variable {𝔽 n} [LinearOrderedField 𝔽] (p q : LinearSystem 𝔽 n)

open Matrix

@[simp] lemma mem_toSet : x ∈ p.toSet ↔ p.mat *ᵥ x ≤ p.vec := Set.mem_setOf

@[simp] theorem toSet_concat : (p.concat q).toSet = p.toSet ∩ q.toSet := by
  simp_rw [Set.ext_iff, Set.mem_inter_iff]
  intro x
  constructor <;> intro h
  . simp_rw [concat, mem_toSet, Pi.le_def] at h
    constructor <;> (rw [mem_toSet, Pi.le_def]; intro i)
    . have := h (i.castLE $ Nat.le_add_right ..)
      simp_all [mulVec]
    . have := h ⟨p.m + i, Nat.add_lt_add_left i.prop ..⟩
      simp_all [mulVec]
  . simp_rw [concat, mem_toSet, Pi.le_def]
    intro i
    by_cases hi : i < p.m <;> simp only [hi, mulVec, ↓reduceDIte, of_apply]
    . apply h.1
    . apply h.2

-- section repr
-- open Std.Format

-- instance repr [Repr 𝔽] : Repr (LinearSystem 𝔽 n) where
--   reprPrec p _p :=
--     (text "!!{ x | "
--       ++ (nest 2 <| reprArg p.mat ++ text " x ≤ " ++ reprArg p.vec)
--       ++ text "}")

-- end repr
