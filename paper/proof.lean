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

--------------------------------------------------------------------------------
--                                   PCP                                      --
--------------------------------------------------------------------------------

-- Defining PCP
structure pcp
  {n : ℕ}
  (Γ : Type)
  (tops : vector (list Γ) n)
  (bottoms : vector (list Γ) n) : Type

namespace pcp
  open vector

  -- Defining the composition of a vector of symbols by a sequence. Used to
  -- define the existence of a solution for PCP.
  def compose
    {Γ : Type}
    {n : ℕ} :
      Π (symbols : vector (list Γ) n), list (fin n) → list Γ
        | symbols list.nil        := list.nil
        | symbols (list.cons i l) :=
          list.append
            (nth symbols i)
            (compose symbols l)

  -- The property of an instance of PCP having a solution. In plain English,
  -- an instance of PCP has a solution iff there exists a sequence of indicies
  -- such that the composition of the indexed tops and bottoms are equal.
  def has_solution
    {n : ℕ}
    {Γ : Type}
    {tops : vector (list Γ) n}
    {bottoms : vector (list Γ) n} :
      pcp Γ tops bottoms → Prop
      | _ := ∃ (seq : list (fin n)), compose tops seq = compose bottoms seq
end pcp

--------------------------------------------------------------------------------
--                             Optimality Theory                              --
--------------------------------------------------------------------------------

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
      (nth s1 (fin.mk i ltin)) ≤
      (nth s2 (fin.mk i ltin)) ∧
        ∀ (j : ℕ), Π (ltji : j < i),
          (nth s1 ⟨j, lt.trans ltji ltin⟩) =
          (nth s2 ⟨j, lt.trans ltji ltin⟩)


  -- TODO: Define the rest of OT
end ot

--------------------------------------------------------------------------------
--                                  Proof                                     --
--------------------------------------------------------------------------------

-- Step 1. Reduce from an arbitrary case of PCP to a case of PCP where there
--         exist only two characters.

-- Definition of a binary language
inductive bin
  | a : bin
  | b : bin

def alphabet_width : Type → ℕ := sorry

def map_to_binary
  {n : ℕ}
  {Γ : Type}

  {tops : vector (list Γ) n}
  {bottoms : vector (list Γ) n}

  {new_tops : vector (list bin) (n * alphabet_width Γ)}
  {new_bottoms : vector (list bin) (n * alphabet_width Γ)}:
    pcp Γ tops bottoms → pcp bin new_tops new_bottoms :=
      sorry

-- TODO: Debug it
-- theorem binary_equivalence {n : ℕ}
--                            {Γ : Type}
--                            {tops bottoms : vector (list Γ) n}
--                            (problem : pcp Γ tops bottoms) :
--   problem.has_solution ↔ (map_to_binary problem).has_solution :=
--   begin
--     split,
--     sorry,
--   end

-- Step 2. Provide our mapping from an arbitrary instance of PCP to an arbitrary
--         instance of OT.

-- TODO

-- Step 3. Show that PCP has a solution if and only if our mapped version of OT
--         has a solution.

-- TODO


--------------------------------------------------------------------------------
--                             Misc / Testing                                 --
--------------------------------------------------------------------------------

-- Proving that a simple instance of PCP has a solution.
namespace hidden_has_solution
  inductive Γ
    | a : Γ
    | b : Γ

  open Γ

  def top_l := [[b], [a]]
  def bot_l := [[], [b, a]]

  def tops : vector (list Γ) 2 := ⟨top_l, by refl⟩
  def bottoms : vector (list Γ) 2 := ⟨bot_l, by refl⟩

  theorem simple_pcp (problem : pcp Γ tops bottoms) : problem.has_solution :=
  begin
    existsi [[
      (0 : fin 2),
      (1 : fin 2)
    ]],
    refl,
  end

  #print simple_pcp
end hidden_has_solution

namespace hidden_score
  open ot
  open vector

  def x : score 5 := ⟨[0, 0, 1, 3, 5], by refl⟩
  def y : score 5 := ⟨[0, 0, 2, 1, 7], by refl⟩

  example : (score_lte x y) :=
  begin
    existsi 2,
    intro ltin,

    rw x,
    rw y,

    split,

    {
      repeat {rw nth},
      repeat {rw list.nth_le},

      exact
        nat.less_than_or_equal.step
        (nat.less_than_or_equal.refl 1),
    },

    {
      intros j ltji,

      repeat {rw nth},

      cases j,
      any_goals { cases j },
      any_goals {
        repeat {rw list.nth_le},
      },

      have h : j < 0,
      from nat.le_of_succ_le_succ (nat.le_of_succ_le_succ ltji),

      exfalso,
      exact (nat.not_lt_zero j) h,
    },
  end
end hidden_score

-- NOTE: This example shows that our definition of ordering for score vectors is
--       broken. We can show that x ≤ y, even though in fact x > y. I should
--       change the defn above to be a conjunct, rather than an implication.
--       I.e. (i < n) ∧ ..., not (Π (ltin : i < n), ...
namespace hidden_break_score
  open ot
  open vector

  def x : score 5 := ⟨[0, 0, 2, 3, 5], by refl⟩
  def y : score 5 := ⟨[0, 0, 1, 1, 7], by refl⟩

  example : (score_lte x y) :=
    begin
      existsi 5,
      assume h,

      have h' : 0 < 0,
      sorry,

      exfalso,
      exact (nat.not_lt_zero 0) h',
    end




end hidden_break_score
