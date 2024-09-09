import Lake
open Lake DSL

package "lean4-polyhedral-combinatorics" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «PolyhedralCombinatorics» where
  -- add any library configuration options here

lean_lib «Utils» where
  -- add any library configuration options here
