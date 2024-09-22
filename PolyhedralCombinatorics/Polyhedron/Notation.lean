import PolyhedralCombinatorics.Polyhedron.Basic
import PolyhedralCombinatorics.LinearSystem.Notation

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

open Lean.Parser Lean.Elab.Term

@[inherit_doc ofLinearSystem]
scoped notation:max (name := matVecPolyhedron) "P(" A " , " b ")" => ofLinearSystem $ of A b

/-- Syntax for declaring polyhedra as systems of linear constraints. -/
syntax:max (name := systemPolyhedron)
  "!P" ("[" term:90 "^" term "]")? "{" linConstraint,*,? "}" : term

macro_rules
  | `(!P[$t^$n]{$[$constraints],*}) => `(ofLinearSystem !L[$t^$n]{$constraints,*})
  | `(!P{$[$constraints],*}) => `(ofLinearSystem $ !L{$constraints,*})

example := !P[ℚ^2]{2 • x_[1] ≤ 1}
example : Polyhedron 𝔽 2 := !P{2 • x_[1] ≤ 1, x_[0] + x_[1] = 0}
