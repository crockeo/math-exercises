-- Title: Generation in Optimality Theory with Lexical Insertion is Undecidable
--
-- Author: Cerek Hillen
--
-- Description:
--   Here we show that PCP is reducible to OT. In particular, we show that when
--   there exists a solution to PCP, there exists a solution to OT, and when
--   there does not exist a solution to PCP, there does not exist a solution to
--   OT.
--
--   Because PCP is known to be Turing Complete, this reduction proves that OT
--   is also Turing Complete.

import data.vector

universes u v

--------------
-- Learning --

-- Defining a DFA as a tuple of its components
structure DFA (Q) (Γ) (δ : Q → Γ → Q) (q0 : Q) (F : set Q) : Type 2

-- Defining whether a DFA accepts a string
def arg_accept (Q)
               (Γ)
               (δ : Q → Γ → Q)
               (F : set Q) : Q → list Γ → Prop
  | q list.nil := F q
  | q (list.cons γ l) := arg_accept (δ q γ) l

def accepts {Q}
            {Γ}
            {δ : Q → Γ → Q}
            {q0 : Q}
            {F : set Q} :  DFA Q Γ δ q0 F → list Γ → Prop :=
  (λ _ l, arg_accept Q Γ δ F q0 l)

-- A concrete example of a DFA accepting a string.
section
  inductive Q
    | qstart : Q
    | qlose : Q

  inductive Γ
    | a : Γ
    | b : Γ

  open Q
  open Γ

  def δ : Q → Γ → Q
    | qstart a := qstart
    | qstart b := qlose
    | qlose  _ := qlose

  def q0 := qstart

  def F : set Q
    | qstart := true
    | _      := false

  variable (dfa : DFA Q Γ δ q0 F)

  #reduce accepts dfa [a, a, a]
end


------------
-- Shared --

-- TODO:
--   * Describe an alphabet type
--   * Describe a string type, such that it's constrained within the alphabet


---------
-- PCP --

namespace pcp
  -- TODO:
  --   * Define a domino type, aka a (string × string)
  --   * Define an instance of PCP, aka a (vec domino i)
  --   * Define an instance of PCP having a solution, i.e. a sequence of
  --     integers s.t. the concatenation of the top strings is equal to the
  --     concatenation of the bottom strings.

  structure PCP (Γ) (a : list Γ) : Type

  -- TODO: Figure out how to do literally anything in Lean
end pcp

-- TODO: Describe PCP here

-----------------------
-- Optimality Theory --

namespace ot
  open vector

  -- We define a score to be a vector of natural numbers of length n. Each value
  -- score_i corresponds to the number of violations that occurred in the ith
  -- constraint.
  def score (n : ℕ) := vector ℕ n

  -- We define an ordering on scores such that s₁ ≤ s₂ iff they are equal up to
  -- some index i, wherein s₁[i] ≤ s₂[i].
  --
  -- TODO: This definition isn't going to work, because you can prove it by
  --       using an index larger than n for i.
  def score_lte {n : ℕ} (s1 : score n) (s2 : score n) : Prop :=
    ∃ (i : ℕ), Π (ltin : i < n),
      (nth s1 ⟨i, ltin⟩) ≤
      (nth s2 ⟨i, ltin⟩) ∧
        ∀ (j : ℕ), Π (ltji : j < i),
          (nth s1 ⟨j, lt.trans ltji ltin⟩) =
          (nth s2 ⟨j, lt.trans ltji ltin⟩)

  def x : score 5 := ⟨[0, 0, 1, 3, 5], rfl⟩
  def y : score 5 := ⟨[0, 0, 2, 1, 7], rfl⟩

  example : (score_lte x y) :=
  begin
    existsi 2,
    intro ltin,

    split,
    {

      sorry,
    },

    {
      intros j ltji,

      have jtj5 : j < 5,
      from lt.trans ltji ltin,

      sorry,
    },
  end

  #reduce (score_lte x y)

  -- TODO: Define the rest of OT
end ot

-----------
-- Proof --

-- TODO
--
-- Want to show that PCP ≤ OT, so we need to show that:
--
--   When there exists a solution to PCP, there exists a solution to OT.
--
--   When there exists no solution to PCP, there exists no solution to OT.
