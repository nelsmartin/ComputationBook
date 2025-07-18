import Mathlib.Data.Countable.Small
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.NormNum
-- import Mathlib.Computability.Language
/-
The following is an attempt to understand Mathlibs implementation of DFAs and
NFAs. I will copy down their code and explain anything I don't understand along
the way.
-/

universe u v


structure DFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Q
  q₀ : Q
  F : Set Q

variable {Q : Type u} {σ : Type v}

namespace DFA

/- TODO: Make DFA inductive, and give it a product constructor so that Prod M1 M2 is a DFA-/

/-- `M.evalFrom s x` evaluates `M` with input `x` starting from the state `s`. -/


@[simp]
def evalFrom (M : DFA Q σ) (s : Q) : List σ → Q :=
  List.foldl M.δ s

/-Running on empty string doesn't change state.-/
theorem evalFrom_nil (M : DFA Q σ) (s : Q) : evalFrom M s [] = s :=
  rfl

/-Running DFA on string of length 1 is the same as applying step once.-/
@[simp]
theorem evalFrom_singleton (M : DFA Q σ) (s : Q) (a : σ) : evalFrom M s [a] = M.δ s a :=
  rfl

/-Running a DFA on a string x with `a` appended gives the same state as
running on the string x and then stepping from that state using `a`. -/
@[simp]
theorem evalFrom_append_singleton (M : DFA Q σ) (s : Q) (x : List σ) (a : σ) :
  evalFrom M s (x ++ [a]) = M.δ (evalFrom M s x) a := by
    simp[evalFrom]

/-- `M.eval x` evaluates `M` with input `x` starting from the state `M.start`. -/
@[simp]
def eval (M : DFA Q σ): List σ → Q :=
  evalFrom M M.q₀

@[simp]
theorem eval_nil (M : DFA Q σ) : eval M [] = M.q₀ :=
  rfl

@[simp]
theorem eval_singleton (M : DFA Q σ) (a : σ) : eval M [a] = M.δ M.q₀ a :=
 rfl

@[simp]
theorem eval_append_singleton (M : DFA Q σ) (x : List σ) (a : σ) :
eval M (x ++ [a]) = M.δ (eval M x) a :=
  evalFrom_append_singleton _ _ _ _

theorem evalFrom_of_append (M : DFA Q σ) (start : Q) (x y : List σ) :
  evalFrom M start (x ++ y) = evalFrom M (evalFrom M start x) y :=
  List.foldl_append


@[simp]
def acceptsFrom (M : DFA Q σ) (s : Q) : Set (List σ) := {x | evalFrom M s x ∈ M.F}

@[simp]
def L (M : DFA Q σ) : Set (List σ) := acceptsFrom M M.q₀

/- Proof that the textbook definitions and the lean definitions imply each other. -/
@[simp]
def accepts' (M : DFA Q σ) (x : List σ) :=
  ∃ r : Fin (x.length + 1) → Q,
  (r 0 = M.q₀) ∧
  (∀ i : Fin (x.length), M.δ (r (i.castSucc)) x[i] = r (i.castSucc + 1)) ∧
  (r ⟨ x.length, by simp ⟩ ∈ M.F)

def L' (M : DFA Q σ) : Set (List σ) := {x | accepts' M x}

theorem lang_def_eq (M : DFA Q σ) (x : List σ) : x ∈ L M ↔ x ∈ L' M := by
  unfold L L' acceptsFrom accepts' evalFrom
  apply Iff.intro
  · intro hx
    exists fun i => List.foldl M.δ M.q₀ (x.take i.val)
    constructor
    · simp
    · constructor
      · intro i
        simp
        have : List.take (↑i + 1) x = List.take (↑i) x ++ [x[↑i]] := by simp
        rw[this,List.foldl_concat]
        rfl
      · simp
        exact hx
  · intro ⟨r, h_init, h_trans, h_accept⟩
    simp
    have : ∀ i : Fin (x.length + 1), r i = List.foldl M.δ M.q₀ (x.take i) := by
      intro i
      induction i using Fin.induction with
      | zero => simp; exact h_init
      | succ i ih =>
      simp at h_trans
      rw[←h_trans i]
      have : List.take (i.succ) x = List.take (↑i) x ++ [x[↑i]] := by simp
      rw[this,List.foldl_concat,ih]
      rfl
    have final_eq := this ⟨x.length, by simp⟩
    rw[final_eq] at h_accept; simp at h_accept
    exact h_accept











variable {Q₁ : Type u}
universe w
variable {Q₂ : Type w} (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ)

@[simp]
def product_of_automata (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ) :
DFA (Q₁ × Q₂) σ :=
⟨
  fun (q₁, q₂) s => (M₁.δ q₁ s, M₂.δ q₂ s),
  (M₁.q₀, M₂.q₀),
  { (q₁, q₂) | (q₁ ∈ M₁.F) ∨ (q₂ ∈ M₂.F) }
⟩


@[simp]
theorem foldl_prod_eq (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ) (x : List σ) :
  List.foldl (product_of_automata M₁ M₂).δ (product_of_automata M₁ M₂).q₀ x =
  ((List.foldl M₁.δ M₁.q₀ x), (List.foldl M₂.δ M₂.q₀ x)) := by
  simp
  exact
  List.foldl_hom₂ x Prod.mk M₁.δ M₂.δ (fun x s ↦ (M₁.δ x.1 s, M₂.δ x.2 s)) M₁.q₀ M₂.q₀ fun a b ↦
  congrFun rfl


open Set
-- have h : M = prod of automata
theorem regular_languages_closed_under_union (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ)
: ∃ Q : Type (max u w), ∃ (M : DFA Q σ), L M = L M₁ ∪ L M₂ := by
exists Q₁ × Q₂
exists product_of_automata M₁ M₂
unfold L
rw[Subset.antisymm_iff,subset_def,subset_def]
simp only [acceptsFrom,evalFrom]
constructor
· intro x hx;
  cases hx with
  | inl hl =>
    rw[foldl_prod_eq M₁ M₂ x] at hl; simp at hl
    exact Or.inl hl
  | inr hr =>
    rw[foldl_prod_eq M₁ M₂ x] at hr; simp at hr
    exact Or.inr hr
· intro x hx
  cases hx with
  | inl hl =>
  exact Or.inl (by rw[foldl_prod_eq M₁ M₂ x]; simp; exact hl)
  | inr hr =>
  exact Or.inr (by rw[foldl_prod_eq M₁ M₂ x]; simp; exact hr)


end DFA

structure NFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Set Q
  q₀ : Q
  F : Set Q

namespace NFA


def stepSet (M : NFA Q σ) (S : Set Q) (a : σ) : Set Q :=
  ⋃ s ∈ S, M.δ  s a

theorem mem_stepSet {s : Q} {S : Set Q} {a : σ} (M : NFA Q σ) :
s ∈ stepSet M S a ↔ ∃ t ∈ S, s ∈ M.δ t a := by
  simp [stepSet]

@[simp]
theorem stepSet_empty (M : NFA Q σ) (a : σ) : stepSet M ∅ a = ∅ := by simp [stepSet]

@[simp]
theorem stepSet_singleton (M : NFA Q σ) (s : Q) (a : σ) : stepSet M {s} a = M.δ s a := by
  simp [stepSet]


/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
  of `S`. -/
def evalFrom (M : NFA Q σ) (S : Set Q) : List σ → Set Q :=
  List.foldl (stepSet M) S

@[simp]
theorem evalFrom_nil (M : NFA Q σ) (S : Set Q) : evalFrom M S [] = S :=
  rfl

@[simp]
theorem evalFrom_singleton (M : NFA Q σ) (S : Set Q) (a : σ) :
evalFrom M S [a] = stepSet M S a :=
  rfl

@[simp]
theorem evalFrom_cons (M : NFA Q σ) (S : Set Q) (a : σ) (x : List σ) :
    evalFrom M S (a :: x) = evalFrom M (stepSet M S a) x :=
  rfl


@[simp]
theorem evalFrom_append_singleton (M : NFA Q σ) (S : Set Q) (x : List σ) (a : σ) :
    evalFrom M S (x ++ [a]) = stepSet M (evalFrom M S x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]


variable (M) in
@[simp]
theorem evalFrom_biUnion (M : NFA Q σ) {ι : Type*} (t : Set ι) (f : ι → Set Q) :
    ∀ (x : List σ), evalFrom M (⋃ i ∈ t, f i) x = ⋃ i ∈ t, evalFrom M (f i) x
  | [] => by simp
  | a :: x => by simp [stepSet, evalFrom_biUnion M _ _ x];


theorem evalFrom_eq_biUnion_singleton (M : NFA Q σ) (S : Set Q) (x : List σ) :
    evalFrom M S x = ⋃ s ∈ S, evalFrom M {s} x := by
  simp [← evalFrom_biUnion]


theorem mem_evalFrom_iff_exists (M : NFA Q σ) {s : Q} {S : Set Q} {x : List σ} :
    s ∈ evalFrom M S x ↔ ∃ t ∈ S, s ∈ evalFrom M {t} x := by
  rw [evalFrom_eq_biUnion_singleton]
  simp


/-- `M.eval x` computes all possible paths though `M` with input `x` starting at an element of
  `M.start`. -/
def eval (M : NFA Q σ) : List σ → Set Q :=
  evalFrom M {M.q₀}


@[simp]
theorem eval_nil (M : NFA Q σ) : eval M [] = {M.q₀}  :=
  rfl

variable (M) in
@[simp]
theorem eval_singleton (M : NFA Q σ) (a : σ) : eval M [a] = stepSet M {M.q₀} a :=
  rfl

variable (M) in
@[simp]
theorem eval_append_singleton (M : NFA Q σ) (x : List σ) (a : σ) :
eval M (x ++ [a]) = stepSet M (eval M x) a :=
  evalFrom_append_singleton ..

variable (M) in
/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
def L (M : NFA Q σ): Set (List σ) := {x | ∃ S ∈ M.F, S ∈ eval M x}

theorem mem_accepts {x : List σ} (M : NFA Q σ) :
x ∈ L M ↔ ∃ S ∈ M.F, S ∈ evalFrom M {M.q₀} x := by
  rfl

end NFA
