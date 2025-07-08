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

<style>
details > summary {
  margin-bottom: 0;
  padding-bottom: 0;
}

details[open] > summary {
  margin-bottom: 0;
  padding-bottom: 0;
}

details > pre,
details > .details-content {
  margin-top: 0;
}
pre {
  margin-top: 0;
}
code.language-lean.hljs {
  padding: 0;
}
</style>

<details>
  <summary><code class="language-lean">theorem not_gt_to_le {a : DCut} : ¬ 0 < a ↔ a ≤ 0 := by
</code></summary>
  <pre><code class="language-lean">  constructor
  . have := trichotomy_lt 0 a
    apply Or.elim this
    . intro h1 h2
      simp_all
    . intro h1 h2
      simp_all
      apply le_of_lt.mpr
      rw[Eq.comm]
      exact h1
  . intro h1 h2
    apply le_of_lt.mp at h1
    simp_all[DCut.ext_iff,lt_inst]
    have ⟨ h3, h4 ⟩ := h2
    simp_all
    apply Or.elim h1
    . intro h
      exact h3 (id (Eq.symm h))
    . intro ⟨ h5, h6 ⟩
      have : A 0 = a.A := by exact Set.Subset.antisymm h4 h6
      exact h3 this</code></pre>

</details>