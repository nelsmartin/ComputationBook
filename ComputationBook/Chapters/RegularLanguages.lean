/-Maybe if I start with a comment it will work beter. -/


import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

variable {α : Type*}
variable (A B : Set α)
open Set
theorem DeMorgan's : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  exact compl_union A B -- given by apply?

/- Do comments get passed through correctly? -/
