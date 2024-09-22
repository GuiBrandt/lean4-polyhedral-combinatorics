import PolyhedralCombinatorics.LinearSystem.LinearConstraints

namespace LinearSystem
open Matrix

variable {𝔽} [LinearOrderedField 𝔽] {n : ℕ}

open Lean.Parser Lean.Elab.Term

/-- Syntax for addressing variables in linear constraints.

  `x_[n]` is shorthand for `Pi.single n 1`. -/
notation "x_[" n "]" => Pi.single (n : Fin _) 1

/-- Syntax category for linear constraints used to define polyhedra. -/
declare_syntax_cat linConstraint
syntax:60 term:61 " ≤ " term : linConstraint
syntax:60 term:61 " <= " term : linConstraint
syntax:60 term:61 " = " term : linConstraint
syntax:60 term:61 " ≥ " term : linConstraint
syntax:60 term:61 " >= " term : linConstraint

/-- Syntax for declaring polyhedra as systems of linear constraints. -/
syntax:max (name := linSystem)
  "!L" ("[" term:90 "^" term "]")? "{" linConstraint,*,? "}" : term

macro_rules
  | `(!L[$t^$n]{$[$constraints],*}) => `((!L{$constraints,*} : LinearSystem $t $n))
  | `(!L{$[$constraints],*}) => do
    let constraints ← constraints.mapM (fun
      | `(linConstraint| $x:term ≤ $y:term) => `(LinearConstraint.le $x $y)
      | `(linConstraint| $x:term <= $y:term) => `(LinearConstraint.le $x $y)
      | `(linConstraint| $x:term = $y:term) => `(LinearConstraint.eq $x $y)
      | `(linConstraint| $x:term ≥ $y:term) => `(LinearConstraint.ge $x $y)
      | `(linConstraint| $x:term >= $y:term) => `(LinearConstraint.ge $x $y)
      | _ => Lean.Macro.throwUnsupported)
    `(ofConstraints [$constraints,*])

example := !L[ℚ^2]{2 • x_[1] ≤ 1}
example : LinearSystem 𝔽 2 := !L{2 • x_[1] ≤ 1, x_[0] + x_[1] = 0}
