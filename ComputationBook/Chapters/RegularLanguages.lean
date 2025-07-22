/- # Regular Languages and Finite Automata

## Overview

The following is a description of deterministic and nondeterministic finite automata in Lean, along with \
a description of regular languages and proofs of a handful of elementary theorems.

The definitions and proofs come from the book Introduction to the Theory of Computation, 3rd ed. by \
Michael Sipser (hereafter "the book"). I would highly recommend reading chapter one in parallel with \
the material below to see helpful graphics and read more in-depth explanations than I provide.

My implementation of finite automata in Lean is based on Mathlib's Computability module.

## Deterministic Finite Automata

Finite automata are simple models of computers. We will start by defining **deterministic** finite automata \
(DFAs) in particular. A visual example is the best way to initially learn about them, so I recommend \
that you look at Figure 1.4 and the following description in the book if you are unfamiliar. \

To summarize: DFAs are simple machines that either *accept* or *reject* strings of symbols. They \
start in their *start state*, and then transition from state to state according to their *transitions*
(the arrows pointing from state to state) based on the current symbol being read from the input string.

If, when done reading the string, the machine is in an *accept state*, the string is *accepted*, and if
not, the string is *rejected*.

State diagrams, like the one depicted in Figure 1.4, are great for intuitively understanding DFAs, but in
order to fomally reason about them, we will formally describe them:
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation

universe u v

structure DFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Q  -- Delta (transition) function
  q₀ : Q         -- Start state
  F : Set Q      -- Accept states

/-
We represent DFAs in Lean as a structure that takes two types as parameters. `Q` \
is the type of the states of the DFA. For example, if `Q` was `Nat`, the DFA \
could be in state 0, 1, 2, 3, ... (but then of course it would no longer be a *finite* \
automaton). Similarly, `σ` is the type of the alphabet.

`δ` is the transition function. It has type `Q → σ → Q` because it takes a state and a symbol \
and returns the state the DFA transitions into. `q₀` is the start state, and `F` is the set of \
accept states.

Let's look at an example of a concrete DFA that can be in one of two states, `q₁` and \
`q₂`. The states of a DFA are represented by a type, so we define an inductive type with only two \
constructors:
-/

inductive state where
| q₁ : state
| q₂ : state

/-
If inductive types in Lean are new to you, the above is basically declaring a new type called \
`state`, and if a term is of type `state`, it is either `q₁` or `q₂`. The DFA will be able to
read `0` or `1` as symbols, so the type of our alphabet σ will be `Fin 2`. If a term is of type
`Fin 2`, that means it is a natural number less than or equal to `2`, or in other words, `0` or
`1`.
-/
namespace state

def M₂ : DFA (state) (Fin 2) :=
⟨
  fun x s => match x with
  | q₁ => match s with | 0 => q₁ | 1 => q₂
  | q₂ => match s with | 0 => q₁ | 1 => q₂,
  q₁,
  {q₂}
⟩

end state


@[simp]
def accepts {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) :=
  ∃ r : Fin (w.length + 1) → Q,
  (r 0 = M.q₀) ∧
  (∀ i : Fin (w.length), M.δ (r (i.castSucc)) w[i] = r (i.castSucc + 1)) ∧
  (r ⟨ w.length, by simp ⟩ ∈ M.F)


def L_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) : Set (List σ) := {w | accepts M w}

@[simp]
def run_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) (steps : Fin (w.length + 1)): Q :=
  match steps with
  | 0 => M.q₀
  | ⟨ k + 1, h ⟩  =>
    let h : k < w.length + 1 := by omega
    M.δ (run_DFA M w ⟨ k, h ⟩) w[k]




universe w

def product_of_automata {Q₁ : Type u} {Q₂ : Type w} {σ : Type v} (M₁ : DFA Q₁ σ) (M₂ : DFA Q₂ σ) :
DFA (Q₁ × Q₂) σ :=
⟨
  fun (q₁, q₂) s => (M₁.δ q₁ s, M₂.δ q₂ s),
  (M₁.q₀, M₂.q₀),
  { (q₁, q₂) | (q₁ ∈ M₁.F) ∨ (q₂ ∈ M₂.F) }
⟩

def run_DFA1 {Q₁ : Type u} {Q₂ : Type w} {σ : Type v} (M₂ : DFA Q₂ σ) (w : List σ)
(r : Fin (w.length + 1) → Q₁) :
  Fin (w.length + 1) → Q₁ × Q₂ := fun x => (r x, run_DFA M₂ w x)

def run_DFA2 {Q₁ : Type u} {Q₂ : Type w} {σ : Type v} (M₁ : DFA Q₁ σ) (w : List σ)
(r : Fin (w.length + 1) → Q₂) :
  Fin (w.length + 1) → Q₁ × Q₂ := fun x => (run_DFA M₁ w x, r x)


open Set

theorem regular_languages_closed_under_union {Q₁ : Type u} {Q₂ : Type w} {σ : Type v}
(M₁ : DFA Q₁ σ)
(M₂ : DFA Q₂ σ) :
∃ Q : Type (max u w), ∃ M : DFA Q σ, L_DFA M = L_DFA M₁ ∪ L_DFA M₂ := by
  exists Q₁ × Q₂
  exists product_of_automata M₁ M₂
  rw[Subset.antisymm_iff,subset_def,subset_def,union_def]
  unfold product_of_automata
  constructor
  · intro w  ⟨ r, h_intro, h_trans, h_accept⟩
    unfold L_DFA accepts; simp; simp at h_intro h_trans h_accept
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
  · unfold L_DFA accepts; simp
    intro w hw
    cases hw with
    | inl hl =>
      obtain ⟨r, h_init, h_trans, h_accept⟩ := hl
      exists run_DFA1 M₂ w r
      unfold run_DFA1
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
      exists run_DFA2 M₁ w r
      unfold run_DFA2
      exact ⟨
        by unfold run_DFA; simp; exact ⟨ rfl, h_init ⟩,
        by intro i; simp; exact ⟨
          by unfold run_DFA; conv => { rhs; unfold run_DFA; simp }; rfl,
          by exact h_trans i
        ⟩,
        by apply Or.inr; simp; exact h_accept⟩



structure NFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Set Q
  q₀ : Q
  F : Set Q

def accepts_NFA {Q : Type u} {σ : Type v} (M : NFA Q σ) (w : List σ) :=
  ∃ r : Fin (w.length + 1) → Q,
  (r 0 = M.q₀) ∧
  (∀ i : Fin w.length, r (i.castSucc + 1) ∈ M.δ (r i.castSucc) w[i]) ∧
  (r ⟨ w.length, by simp ⟩  ∈ M.F)


/-
You might have noticed something at this point: these proofs are getting
long! That's largely because generating these sequences of states and then
proving that they satisfy the langauge acceptance conditions comes with a lot of
overhead. It would be easier if we could define the acceptance of a string by
a DFA or an NFA as: when the machine runs with respect to that string, it ends
up in an accept state. That way, instead of construcing these runs of states,
we could just run the machine. To use this simpler definition, let's prove
that it's equivalent to the accepts_NFA definition above.
-/


/-First, we define a run and a step function for our NFA:-/










def L_NFA {Q : Type u} {σ : Type v} (M : NFA Q σ) : Set (List σ) :=
  {w | accepts_NFA M w}

@[simp]
 def run_NFA {Q : Type u} {σ : Type v}
 (M : NFA Q σ) (w : List σ) (steps : Fin (w.length + 1)) : Set Q :=
    match steps with
    | ⟨ 0, _ ⟩  => {M.q₀}
    | ⟨ k + 1, h ⟩ =>
      let h : k < w.length + 1 := by omega
      ⋃ r ∈ (run_NFA M w ⟨ k, h ⟩ ), M.δ r w[k]



def NFA_step {Q : Type u} {σ : Type v} (N : NFA Q σ) (prev_states : Set Q) (s : σ) : Set Q :=
  ⋃ q ∈ prev_states, N.δ q s

/- And a run function: -/
def NFA_run {Q : Type u} {σ : Type v} (N : NFA Q σ) (w : List σ) : Set Q :=
  w.foldl (NFA_step N) {N.q₀}

#check List.foldl
/-
Now, let's define the language of an NFA as the set of strings
that are accepted by the NFA.
-/

def L_NFA' {Q : Type u} {σ : Type v} (N : NFA Q σ) : Set (List σ) :=
  {w | ∃ r ∈ NFA_run N w, r ∈ N.F}

/-To incrementally prove acceptance: verify induction step here-/

/-if r i = q and q ∈ run_DFA w[:i], → r i + 1 ∈ run_DFA w[:i + 1 -/
def induction_helper {Q : Type u} {σ : Type v} (N : NFA Q σ) (w : List σ)
(r : Fin (w.length + 1) → Q)
(h_trans : ∀ (i : Fin w.length), r (i.castSucc + 1) ∈ N.δ (r i.castSucc) w[i]) :
∀ i : Fin w.length,
    -- Maybe I need the last few bits of the list here instead of head.
    r i.castSucc ∈ NFA_run N (w.take ↑i) →
    r i.succ ∈ NFA_run N (w.take (↑i + 1)) := by
  intro i h_prev
  unfold NFA_run NFA_step
  cases w with
  | nil =>
    cases i; trivial
  | cons x xs =>

    unfold NFA_run at h_prev;

    sorry

theorem NFA_language_equiv {Q : Type u} {σ : Type v} (N : NFA Q σ) : L_NFA N = L_NFA' N := by
  unfold L_NFA L_NFA'
  rw[Subset.antisymm_iff,subset_def,subset_def]
  constructor
  · intro w ⟨ r, h_init, h_trans, h_accept ⟩

    exists r ⟨ w.length, by simp ⟩
    exact ⟨
      by
      unfold NFA_run NFA_step
      --have : ∀ i : Fin (w.length + 1), r i ∈ NFA_run N w
      sorry
      ,

      h_accept ⟩
  · intro w hw
    sorry









def NFA_to_DFA {Q : Type u} {σ : Type v} (N : NFA Q σ) : DFA (Set Q) σ :=
  ⟨
    (fun R a => ⋃ r ∈ R, N.δ r a),
    ({N.q₀}),
    ({R | ∃ r ∈ R, r ∈ N.F})
  ⟩







theorem DFA_NFA_equivalence {Q : Type u} {σ : Type v} (N : NFA Q σ) :
∃ (Q' : Type u) (M : DFA Q' σ), L_DFA M = L_NFA N := by
  exists (Set Q)
  exists NFA_to_DFA N
  rw[Subset.antisymm_iff,subset_def,subset_def]
  constructor
  · intro w ⟨ r, h_init, h_trans, h_accept ⟩

    unfold L_NFA accepts_NFA
    let finalState : Set Q := r ⟨ w.length , by simp⟩
    unfold NFA_to_DFA at h_accept
    simp at h_accept
    rcases h_accept with ⟨q, hq_in_finalState, hq_in_NF⟩

    sorry




  · intro w ⟨ r, h_init, h_trans, h_accept ⟩
    unfold L_DFA accepts
    exists run_DFA (NFA_to_DFA N) w
    · unfold run_DFA NFA_to_DFA; simp
      exact ⟨
        by rfl,
        by intro i; conv => {rhs; unfold run_DFA; simp}; rfl,
        by
        exists r ⟨ w.length, by simp ⟩
        exact ⟨
          by
          have : ∀ i : Fin (w.length + 1), r i ∈ run_DFA (NFA_to_DFA N) w i := by
            unfold run_DFA NFA_to_DFA
            intro i; simp
            induction i using Fin.induction with
            | zero => rw[h_init]; rfl
            | succ i ih =>
              cases i with | mk i hi =>
              simp [Fin.succ]
              exists r ⟨ i, by exact Nat.lt_add_right 1 hi⟩
              exact ⟨ by unfold run_DFA; exact ih,
                by
                let i_fin : Fin w.length := ⟨i, hi⟩
                have := h_trans i_fin
                simp at this
                exact this
              ⟩
          unfold run_DFA NFA_to_DFA at this
          exact this ⟨ w.length, by simp⟩
          ,
          h_accept⟩ ,
      ⟩

theorem DFA_NFA_equivalence' {Q : Type u} {σ : Type v}
(N : NFA Q σ)
(M : DFA (Set Q) σ)
(h : M = NFA_to_DFA N) :
 L_NFA N = L_DFA M := by
  ext x
  sorry
