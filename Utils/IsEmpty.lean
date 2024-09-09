import Mathlib.Logic.IsEmpty
import Mathlib.Order.Synonym

instance [it : IsEmpty α] : IsEmpty (Lex α) := it

instance [l : IsEmpty α] [r : IsEmpty β] : IsEmpty (α ⊕ β) where
  false
  | .inl x => l.false x
  | .inr x => r.false x
