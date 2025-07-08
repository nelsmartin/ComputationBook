/- # Regular Languages -/


import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

variable {α : Type*}
variable (A B : Set α)
open Set


/-Explain what finite automata are.-/
universe u v

structure DFA (Q : Type u) (σ : Type v) where
  δ : Q → σ → Q
  q₀ : Q
  F : Set Q


/-Maybe some examples -/

inductive state where
| q₁ : state
| q₂ : state

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



@[simp]
def run_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) (steps : Fin (w.length + 1)): Q :=
  match steps with
  | 0 => M.q₀
  | ⟨ k + 1, h ⟩  =>
    let h : k < w.length + 1 := by omega
    M.δ (run_DFA M w ⟨ k, h ⟩) w[k]



def L_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) : Set (List σ) := {w | accepts M w}

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


def NFA_to_DFA {Q : Type u} {σ : Type v} (N : NFA Q σ) : DFA (Set Q) σ :=
  ⟨
    (fun R a => ⋃ r ∈ R, N.δ r a),
    ({N.q₀}),
    ({R | ∃ r ∈ R, r ∈ N.F})
  ⟩
  /-Given that w ∈ L NFA, show that w ∈ L DFA using our run_DFA definition.
    w ∈ L NFA means that there exists a series of states r where
    (1) the first state is in start state of N,
    (2) ∀ i, r (i + 1) ∈ N.δ (r i) w[i], and
    (3) r (w.length) ∈ N.F.

    After the NFA has run, if any of the set of current states is ∈ N.F, the
    word is accepted.

    We need to prove that there is also an DFA that recognizes this same string.
    We contructor our DFA as follows:

    δ := fun (R : Set Q) (s : σ) → ⋃ r ∈ R, N.δ r s
    q₀ := {N.q₀}
    F := {(R : Set Q) | ∃ r ∈ R, r ∈ N.F}

   The type of our DFA is Set Q. The delta function takes in a set of
   states and a letter, and applies N.δ to each state in the set with
   respect to that letter, each of which produces a set of states. These
   sets of states are then all grouped into one happy set.

   M.F is of type Set Set Q. F contains all of the sets of Q that contain
   at least one of the states in N.F.

   There are three criteria for the acceptance of a word by a DFA. I will lay
   them out here and describe for each why the contruction of the DFA from the NFA
   guarentees the satisfaction of that criteria.

  where r i is defined as run_DFA M:

   1. r 0 = M.q₀
    This is known because M.q₀ was set as {N.q₀}.

    2. Delta

    3. We know that the last state is a member of M.F because we are given that
       There exists a run of Q where each Q is a member of the set produced
       By ONE previous state and the previous symbol, and that the last
       state in the run is a member of the accept set of states.

       Therefore, because M.delta is merely combining the sets of states
       produced at each delta function, it is guaraneteed to include
       the run of N states. Therefore, At each step of M, the (r_DFA i) = R : Set Q must contain
       the r_NFA i = r : Q. And it follows that at the last step,
       the final Set Q must contain a state that was part of the origional accept state.
       Therefore, given that we defined the accept state of M as all of the sets that contain
       one of the accept states in N.F, the final Set Q in the DFA run is an accept state.




      Intermediate step: ∀ i, (r i) ∈ run_DFA M i
      Therefore, r (w.length) ∈ run_DFA M i*
      r (w.length) ∈ N.F
      run_DFA M i contains an N.F accept state
      that meets accept state criteria for M.



   -/

theorem DFA_NFA_equivalence {Q : Type u} {σ : Type v} (N : NFA Q σ) :
∃ (Q' : Type u) (M : DFA Q' σ), L_DFA M = L_NFA N := by
  exists (Set Q)
  exists NFA_to_DFA N
  rw[Subset.antisymm_iff,subset_def,subset_def]
  constructor
  · intro w ⟨ r, h_init, h_trans, h_accept ⟩
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
        -- Two tasks: Prove that r : Q is accept state, and that it's in
        -- The final step of the M progression*.

        exact ⟨
          by
          let hx : ∀ i : Fin (w.length + 1), r i ∈ run_DFA (NFA_to_DFA N) w i := by
            unfold run_DFA NFA_to_DFA
            intro i
            induction i using Fin.induction with
            | zero=> simp; rw[h_init]; rfl
            | succ i ih => simp; simp at ih; sorry



          sorry
          ,
          h_accept⟩ ,
      ⟩
