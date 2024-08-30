import PolyhedralCombinatorics.Polyhedron.Basic

namespace Polyhedron
open Matrix LinearSystem

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

open Lean.Parser Lean.Elab.Term LinearConstraint.Comparator

@[inherit_doc ofLinearSystem]
scoped notation:max (name := matVecPolyhedron) "P(" A " , " b ")" => ofLinearSystem $ of A b

/-- Syntax for addressing variables in linear constraints.

  `x_[n]` is shorthand for `Pi.single n 1`. -/
notation "x_[" n "]" => Pi.single n 1

/-- Syntax category for linear constraints used to define polyhedra. -/
declare_syntax_cat linConstraint
syntax:60 term:61 " ≤ " term : linConstraint
syntax:60 term:61 " <= " term : linConstraint
syntax:60 term:61 " = " term : linConstraint
syntax:60 term:61 " ≥ " term : linConstraint
syntax:60 term:61 " >= " term : linConstraint

/-- Syntax for declaring polyhedra as systems of linear constraints. -/
syntax:max (name := systemPolyhedron)
  "!P" ("[" term:90 "^" term "]")? "{" linConstraint,*,? "}" : term

macro_rules
  | `(!P[$t^$n]{$[$constraints],*}) => `((!P{$constraints,*} : Polyhedron $t $n))
  | `(!P{$[$constraints],*}) => do
    let constraints ← constraints.mapM (fun
      | `(linConstraint| $x:term ≤ $y:term) => `(⟨$x, le, $y⟩)
      | `(linConstraint| $x:term <= $y:term) => `(⟨$x, le, $y⟩)
      | `(linConstraint| $x:term = $y:term) => `(⟨$x, eq, $y⟩)
      | `(linConstraint| $x:term ≥ $y:term) => `(⟨$x, ge, $y⟩)
      | `(linConstraint| $x:term >= $y:term) => `(⟨$x, ge, $y⟩)
      | _ => Lean.Macro.throwUnsupported)
    `(ofLinearSystem $ ofConstraints [$constraints,*])

example := !P[ℚ^2]{2 • x_[1] ≤ 1}
example : Polyhedron 𝔽 2 := !P{2 • x_[1] ≤ 1, x_[0] + x_[1] = 0}
