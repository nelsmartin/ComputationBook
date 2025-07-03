 # Regular Languages 
```lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

variable {α : Type*}
variable (A B : Set α)
open Set
theorem DeMorgan's : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  exact compl_union A B -- given by apply?
```
 This is great and all, but the important thing to remember here is that I love my girlfriend. 
