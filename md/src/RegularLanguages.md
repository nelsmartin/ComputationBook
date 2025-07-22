 # Regular Languages and Finite Automata

## Overview
The following is a description of deterministic and nondeterministic finite automata in Lean, followed by a definition of regular languages and proofs of a handful of elementary theorems.

The definitions and proofs come from the book

- [Introduction to the Theory of Computation, 3rd ed](https://cs.brown.edu/courses/csci1810/fall-2023/resources/ch2_readings/Sipser_Introduction.to.the.Theory.of.Computation.3E.pdf).

by Michael Sipser (hereafter "the book"). I would highly recommend reading chapter one in parallel with the material below to see helpful graphics and read more in-depth explanations than I provide.

My implementation of finite automata in Lean is based on [Mathlib's Computability module](https://github.com/leanprover-community/mathlib4/tree/f68fe3b915fc989e0fcd1f6904eab27607f01b9f/Mathlib/Computability).

## Deterministic Finite Automata

Finite automata are simple models of computers. We will start by defining **deterministic** finite automata (DFAs) in particular. A visual example is the best way to learn about them, so I recommend that you look at Figure 1.4 and the following description in the book if you are unfamiliar.

To summarize: DFAs are simple machines that either *accept* or *reject* strings of symbols. They start in their *start state*, and then transition from state to state according to their *transitions* (the arrows pointing from state to state) based on the current symbol being read from the input string.

If, when done reading the string, the machine is in an *accept state*, the string is *accepted*, and if
not, the string is *rejected*.

State diagrams, like the one depicted in Figure 1.4, are great for intuitively understanding DFAs, but in order to formally reason about them, we will formally describe them:

```lean
import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation
set_option linter.style.longLine false

universe u v
variable {Q : Type u} {σ : Type v}


structure DFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Q  -- Delta (transition) function
  q₀ : Q         -- Start state
  F : Set Q      -- Accept states

namespace DFA
```

We represent DFAs in Lean as a structure that takes two types as parameters. `Q` is the type of the states of the DFA. For example, if `Q` was the type `Nat`, the DFA could be in state 0, 1, 2, 3, ... (but then of course it would no longer be a *finite* automaton). Similarly, `σ` is the type of the alphabet.

`δ` is the transition function. It has type `Q → σ → Q` because it takes a state and a symbol and returns the state the DFA transitions into. `q₀` is the start state, and `F` is the set of accept states.

Let's look at an example of a concrete DFA that can be in one of two states, `q₁` and `q₂` (See Example 1.7 in the book). The states of a DFA are represented by a type, so we define an inductive type with only two constructors:

```lean
inductive state where
| q₁ : state
| q₂ : state
```

If inductive types in Lean are new to you, the above is basically declaring a new type called `state`, and if a term is of type `state`, it is either `q₁` or `q₂`. The DFA will be able to read `0` or `1` as symbols, so the type of our alphabet `σ` will be `Fin 2`. Terms of type `Fin 2` must be natural numbers less than or equal to `2`, i.e. `0` or `1`. We now define our DFA with respect to those types:

```lean
namespace state

def M : DFA (state) (Fin 2) :=
⟨
  fun x s => match x with
  | q₁ => match s with | 0 => q₁ | 1 => q₂
  | q₂ => match s with | 0 => q₁ | 1 => q₂,
  q₁,
  {q₂}
⟩

end state
```

The constructor takes three arguments; firstly, the `δ` function, which corresponds to the table:
```
    +---+---+
    | 0 | 1 |
+---+---+---+
| q₁| q₁| q₂|
+---+---+---+
| q₂| q₁| q₂|
+---+---+---+
```
Then the start state `q₁`, and finally the set of accept states: `{q₂}`. This DFA accepts all strings that end in a `1`.

Now that we have a formal definition of DFAs, let's come up with a formal definition for the **acceptance** of a string by a DFA. According to the book, if `M = (Q, σ, δ, q₀, F)` is a DFA and `w = w₁w₂...wₙ` is a string where each `wᵢ` is a member of the alphabet `σ`, then `M` **accepts** `w` if a sequence of states `r₀,r₁,...,rₙ` in `Q` exists with three conditions:

```
1. r₀ = q₀,
2. δ(rᵢ, wᵢ₊₁) = rᵢ₊₁ for i = 0,...,n-1, and
3. rₙ ∈ F.
```

The first criteria checks that the sequence of states starts in M's start state, the second checks that each transition from state to state respects the `δ` function, and the third checks that the last state in the sequence of states is one of M's accept states.

To represent this sequence of states in Lean, we will use a function `r` of type `Fin w.length + 1 → Q`. So, `r 0` will return the first state in the sequence, `r 1` the next, and so on up to the length of `w`. We say that a DFA M **accepts** a string `w` if there exists a sequence of states `r` that respects our three acceptance criteria. In Lean:

```lean
@[simp]
def accepts' {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) :=
  ∃ r : Fin (w.length + 1) → Q,
  (r 0 = M.q₀) ∧
  (∀ i : Fin (w.length), M.δ (r (i.castSucc)) w[i] = r (i.castSucc + 1)) ∧
  (r ⟨ w.length, by simp ⟩ ∈ M.F)
```

We mark the definition with `@[simp]` so that the `simp` tactic can unfold the definition. I called this definition `accepts'` instead of `accepts` because I want to introduce a different, more convenient definition later.

## Regular Languages

A *language* is a set of strings over a given alphabet. A DFA *recognizes* a language if it accepts every string in the language. A language is a *regular language* if some finite automaton recognizes it. In Lean, the language of a DFA can be defined like so:

```lean
def L' {Q : Type u} {σ : Type v} (M : DFA Q σ) : Set (List σ) := {w | accepts' M w}
```
 Therefore, the set of strings recognized by a DFA is regular by definition.

## Regular Operations

The regular operations are operations on languages that preserve their regularity. One such operation is **union**, which is defined as follows:

```
If A and B are languages, A ∪ B = {x | x ∈ A or x ∈ B}
```

In other words, if `A` and `B` are regular languages (sets of strings) then A ∪ B (the combination of all strings in A and B) will *also* be a regular language. Recall that a language is `regular` if some DFA recognizes it, so the above theorem could be restated as: if there is some DFA `M₁` that recognizes a language `A`, and another DFA `M₂` that recognizes a language `B`, then there must exist some DFA `M₃` that accepts all strings in `A ∪ B` (both languages).

In order to prove the above, we must actually construct the DFA `M₃`. Our strategy will be to "simulate" `M₁` and `M₂` with `M₃`, and keep track of what states they would each be in if they were reading the input string.

To that end, if `Q₁` is the type of the states of `M₁` and `Q₂` is the type of the states of `M₂`, `Q₁ × Q₂` will be the type of the states of `M₃`. That is, at any given time, the state of `M₃` is represented by an ordered pair, where the first entry in the pair is one of the original states of `M₁`, and the second entry is one of the original states from `M₂`.

The `δ` function for `M₃` will apply `M₁.δ` to the first entry in the ordered pair, and `M₂.δ` to the second entry. The start state for `M₃` will be the ordered pair `(M₁.q₀, M₂.q₀)`, and the set of accept states will be all states where the first entry in the ordered pair is an accept state for `M₁`, and all states where the second entry is an accept state for `M₂`.

In this way, we have "simulated" `M₁` and `M₂` in `M₃`, and it will accept any string that `M₁` or `M₂` does. I would highly recommend reading Theorem 1.25 in the book for more details on how this proof works.

In Lean, we can define this combination of `M₁` and `M₂` like so:
 
```lean
universe w

@[simp]
def product_of_automata {Q₁ : Type u} {Q₂ : Type w} {σ : Type v}
(M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ) :
DFA (Q₁ × Q₂) σ :=
⟨
  fun (q₁, q₂) s => (M₁.δ q₁ s, M₂.δ q₂ s),
  (M₁.q₀, M₂.q₀),
  { (q₁, q₂) | (q₁ ∈ M₁.F) ∨ (q₂ ∈ M₂.F) }
⟩
```

Before we prove the theorem, let's define a couple of helpful functions. Recall that our definition of acceptance is that there exists a sequence of states `r` that meets the acceptance criteria, so the following will help us generate those sequences of states:

```lean
@[simp]
def run_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ)
(steps : Fin (w.length + 1)): Q :=
  match steps with
  | 0 => M.q₀
  | ⟨ k + 1, h ⟩  =>
    let h : k < w.length + 1 := by omega
    M.δ (run_DFA M w ⟨ k, h ⟩) w[k]


-- Run of states in M₃ if w ∈ L' M₁
def run_DFA_left {Q₁ : Type u} {Q₂ : Type w} {σ : Type v} (M₂ : DFA Q₂ σ) (w : List σ)
(r : Fin (w.length + 1) → Q₁) :
  Fin (w.length + 1) → Q₁ × Q₂ := fun x => (r x, run_DFA M₂ w x)

-- Run of states in M₃ if w ∈ L' M₂
def run_DFA_right {Q₁ : Type u} {Q₂ : Type w} {σ : Type v} (M₁ : DFA Q₁ σ) (w : List σ)
(r : Fin (w.length + 1) → Q₂) :
  Fin (w.length + 1) → Q₁ × Q₂ := fun x => (run_DFA M₁ w x, r x)
```

Now we are ready to prove that the union of two regular languages is a regular language!
## Proof that the Class of Regular Languages is Closed Under the Union Operation

```lean
open Set

theorem regular_languages_closed_under_union {Q₁ : Type u} {Q₂ : Type w} {σ : Type v}
(M₁ : DFA Q₁ σ)
(M₂ : DFA Q₂ σ) :
∃ Q : Type (max u w), ∃ M : DFA Q σ, L' M = L' M₁ ∪ L' M₂ := by
  exists Q₁ × Q₂
  exists product_of_automata M₁ M₂
  rw[Subset.antisymm_iff,subset_def,subset_def,union_def]
  unfold product_of_automata
  constructor
  · intro w  ⟨ r, h_intro, h_trans, h_accept⟩
    unfold L' accepts'; simp; simp at h_intro h_trans h_accept
    cases h_accept with
    | inl hl =>
      apply Or.inl
      exists fun x => (r x).1
      exact ⟨ by simp; rw[h_intro],
              by simp; intro i; rw[←h_trans],
              by simp; exact hl⟩
    | inr hr =>
      apply Or.inr
      exists fun x => (r x).2
      exact ⟨ by simp; rw[h_intro],
              by simp; intro i; rw[←h_trans],
              by simp; exact hr⟩
  · unfold L' accepts'; simp
    intro w hw
    cases hw with
    | inl hl =>
      obtain ⟨r, h_init, h_trans, h_accept⟩ := hl
      exists run_DFA_left M₂ w r
      unfold run_DFA_left
      exact ⟨
        by unfold run_DFA; simp; exact ⟨ h_init, rfl ⟩,
        by intro i; simp; exact ⟨
          by exact h_trans i,
          by unfold run_DFA; conv => { rhs; unfold run_DFA; simp }; rfl
        ⟩,
        by apply Or.inl; simp; exact h_accept
      ⟩
    | inr hr =>
      obtain ⟨r, h_init, h_trans, h_accept⟩ := hr
      exists run_DFA_right M₁ w r
      unfold run_DFA_right
      exact ⟨
        by unfold run_DFA; simp; exact ⟨ rfl, h_init ⟩,
        by intro i; simp; exact ⟨
          by unfold run_DFA; conv => { rhs; unfold run_DFA; simp }; rfl,
          by exact h_trans i
        ⟩,
        by apply Or.inr; simp; exact h_accept⟩
```

Whew! That's a beast of a proof. Its size comes from the fact that in order to prove a given string is accepted by a DFA, we must generate the sequence of states that the DFA transitions through when it reads that string *and* prove that the sequence of states meets the three criteria defined above.

## Alternative Definition of Acceptance

It would be much more convenient to just say: a string is accepted by a DFA if, when run with respect to that string, the DFA ends up in an accept state. No need to generate a sequence of states; just run the DFA and see what happens. This is actually the way Mathlib, Lean's math library, defines acceptance for a DFA in its Computability module. Here is an alternative set of definitions adapted from Mathlib:

```lean
@[simp]
def evalFrom (M : DFA Q σ) (s : Q) : List σ → Q :=
  List.foldl M.δ s

@[simp]
def eval (M : DFA Q σ): List σ → Q :=
  evalFrom M M.q₀
```
Now for the key difference. Instead of generating a sequence of states to prove that a word is accepted, we evaluate the string using the DFA's transition function, and see if the DFA ends up in one of its acceptance states.
 
```lean
@[simp]
def acceptsFrom (M : DFA Q σ) (s : Q) : Set (List σ) := {x | evalFrom M s x ∈ M.F}

@[simp]
def L (M : DFA Q σ) : Set (List σ) := acceptsFrom M M.q₀
```

Now we have an alternative definition of the language of a DFA `L` that we suspect will be easier to use, but is it equivalent to the definition given in the book (our `L'`)? If only there was a way to prove that it was...

Wait a gosh darn minute, this is Lean! We can prove anything! Let's prove that these two definitions imply each other:

## The Definitions of Acceptance Are Equal

```lean
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
```
 Fantastic. Now we can try to reprove the union theorem using our new definition `L`:

```lean
variable {Q₁ : Type u} {Q₂ : Type w} (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ)

-- Helper theorem that lets us apply the δ function to the elements in a pair.
@[simp]
theorem foldl_prod_eq (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ) (x : List σ) :
  List.foldl (product_of_automata M₁ M₂).δ (product_of_automata M₁ M₂).q₀ x =
  ((List.foldl M₁.δ M₁.q₀ x), (List.foldl M₂.δ M₂.q₀ x)) := by
  simp
  exact
  List.foldl_hom₂ x Prod.mk M₁.δ M₂.δ (fun x s ↦ (M₁.δ x.1 s, M₂.δ x.2 s)) M₁.q₀ M₂.q₀ fun a b ↦
  congrFun rfl

theorem regular_languages_closed_under_union_2 (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ)
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
```
 Our redefinition allowed us to shorten our theorem from 49 lines to 26 lines! What a win. Another thing to notice about the Mathlib theorems is that they start from simple definitions and build on one another. That's one of the hallmarks of mature Lean programming: the ability to split a difficult problem or theorem into small, easily digestible parts.

## Nondeterministic Finite Automata

We now move on to nondeterministic finite automata (NFAs). The difference between NFAs and DFAs is that NFAs can be in several states at once (hence their nondeterminism). Here is their formal definition in Lean:

```lean
structure NFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Set Q
  q₀ : Q
  F : Set Q
```
 The only difference between this definition and the definition of the DFA is that for the DFA, the `δ` function has type `Q → σ → Q`, but here, for the NFA, the `δ` function has type `Q → σ → Set Q`. This means that for any given state and symbol, a DFA can go into a *set* of states (as opposed to just one state in the case of the DFA).

To run an NFA, we start at the start state `q₀` and apply the `δ` function to it with respect to the first symbol in the input string. This produces a set of states. We then apply the `δ` function again to each of the states in that set, producing other sets of states. We union those sets together, then repeat the process, applying the `δ` function to each of the states in *that* set.

The NFA accepts a string if *any* of the states in the final set of states produced by running the NFA with respect to that string is an accept state of the NFA. For a more detailed explanation of NFAs, see Chapter 1.2 in the book.

The book's definition of acceptance for NFAs involves generating a sequence of valid states, but let's go straight to the Mathlib definition described above (I leave the proof of their equality as an exercise for the reader). The following definitions are slightly modified from the Mathlib Computability module definitions:

```lean
namespace NFA

def stepSet (M : NFA Q σ) (S : Set Q) (a : σ) : Set Q :=
  ⋃ s ∈ S, M.δ  s a

def evalFrom (M : NFA Q σ) (S : Set Q) : List σ → Set Q :=
  List.foldl (stepSet M) S

def eval (M : NFA Q σ) : List σ → Set Q :=
  evalFrom M {M.q₀}

def L (M : NFA Q σ): Set (List σ) := {x | ∃ S ∈ M.F, S ∈ eval M x}
```

## NFA and DFA Equivalence

We will now set out to prove that for every NFA, there exists a DFA that recognizes the same language. We will use a strategy similar to the one we used earlier: given an NFA, we will construct a DFA guaranteed to accept all of the same strings.

Let's say we are given an NFA `N` with state type `Q`, and we want to construct a DFA `M` that accepts all of the same strings. `N` can be in many states at once, so we let the type of the states of `M` be `Set Q`. At any given time, the state of our DFA is a *set* of the original states of `N`, and these states should correspond to all of the states that the NFA would be in if it saw the same symbols.

We want `M` to transition according to the `δ` function of `N`, so to move `M` from state to state, we apply `N.δ` to each state in the set of states that represents the current state of `M`. `M` accepts a string if, when done running, the `Set Q` that represents its current state contains an accept state of `N`.

This is a somewhat tricky proof very concisely explained; for more detail, see Theorem 1.39 in the book.

In Lean, we construct our DFA from our NFA like so:

```lean
end NFA

@[simp]
def NFA_to_DFA (N : NFA Q σ) : DFA (Set Q) σ :=
  ⟨
    (fun R a => ⋃ r ∈ R, N.δ r a),
    ({N.q₀}),
    ({R | ∃ r ∈ N.F, r ∈ R})
  ⟩
```
The proof that for every NFA there exists an equivalent DFA is now trivial:
```lean
theorem DFA_NFA_equivalence (N : NFA Q σ) :
∃ (Q' : Type u) (M : DFA Q' σ), DFA.L M = NFA.L N := by
  exists Set Q
  exists NFA_to_DFA N
```
