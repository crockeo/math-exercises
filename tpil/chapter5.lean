-- Exercise 1
--
-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you
-- can now with tactic proofs, using also rw and simp as appropriate.

-- NOTE: I had alreadty been doing this, so I don't think I need to go back and
--       do them again... oops.

-- Exercise 2
--
-- Use tactic combinators to obtain a one line proof of the following:
example (p q r : Prop) (hp : p) : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by {
  repeat {split},
  repeat {
    {
      left,
      assumption
    } <|>
    right <|>
    assumption
  }
}
