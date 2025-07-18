/- # Regular Languages -/


import Mathlib.Data.Set.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Matrix.Basic

import Std.Data.HashSet
import Std.Data.HashMap
import Std.Data.HashSet

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

def exampleDFA : DFA (Fin 2) (Fin 2) := ⟨
  fun x s => match x with
  | 0 => match s with | 0 => 1 | 1 => 0
  | 1 => match s with | 0 => 0 | 1 => 1,
  0,
  {1}
⟩

def accepts {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) :=
  ∃ r : Fin (w.length + 1) → Q,
  (r 0 = M.q₀) ∧
  (∀ i : Fin (w.length), M.δ (r (Fin.castSucc i)) w[i] = r (Fin.castSucc i + 1)) ∧
  (r ⟨ w.length, by simp ⟩ ∈ M.F)



@[simp]
def run_DFA {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) (steps : Fin (w.length + 1)): Q :=
  match steps with
  | 0 => M.q₀
  | ⟨ k + 1, h ⟩  =>
    let h : k < w.length + 1 := by omega
    M.δ (run_DFA M w ⟨ k, h ⟩) w[k]


def accepts' {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) :=
  run_DFA M w ⟨ w.length, by simp ⟩  ∈ M.F



theorem acceptsAreSame {Q : Type u} {σ : Type v} (M : DFA Q σ) (w : List σ) :
accepts M w ↔ accepts' M w := by
unfold accepts accepts'
apply Iff.intro
· intro ⟨ r, h_init, h_trans, h_accept ⟩

  let h_starts_equal : r 0 = run_DFA M [] 0 := by unfold run_DFA; exact h_init

  let h_trans_equal : ∀ i' : Fin w.length, r (i'.castSucc) = run_DFA M w (i'.castSucc) →
  r (i'.castSucc + 1) = run_DFA M w (i'.castSucc + 1) := by
    intro i' h_prev
    let hr := h_trans i'
    rw[←hr]
    unfold run_DFA
    simp
    exact congrFun (congrArg M.δ h_prev) w[↑i']

  let h_equal : ∀ i' : Fin (w.length + 1), r i' = run_DFA M w i' := by
    intro i'
    induction i' using Fin.induction with
    | zero => unfold run_DFA; simp; exact h_init
    | succ i' ih =>
    let hx := h_trans_equal i' ih
    let h_fin : i'.castSucc + 1 = i'.succ := by simp
    rw[h_fin] at hx
    exact hx

  let h_end_equal : r ⟨ w.length, by simp ⟩ = run_DFA M w ⟨ w.length, by simp ⟩ := by
    exact h_equal ⟨w.length, by simp ⟩

  rw[←h_end_equal]
  exact h_accept

· intro h
  exists fun x => run_DFA M w x
  constructor
  · unfold run_DFA; simp ;rfl
  · constructor
    · simp
      intro i
      let hx : (run_DFA M w i.succ =  match i.succ with
                                    | 0 => M.q₀
                                    | ⟨ k + 1, h ⟩  =>
                                    let h : k < w.length + 1 := by omega
                                    M.δ (run_DFA M w ⟨ k, h ⟩) w[k]) := by
                                    simp; exact run_DFA.eq_def M w i.succ

      rw[hx]
      simp
      rfl
    · exact h
