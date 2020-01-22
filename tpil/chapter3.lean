-- Exercise 1
--
-- Prove the following identities, replacing the “sorry” placeholders with
-- actual proofs.
section
  variables p q r : Prop

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume hp : p ∧ q,
        show q ∧ p, from and.intro (and.right hp) (and.left hp))
      (assume hq : q ∧ p,
        show p ∧ q, from and.intro (and.right hq) (and.left hq))

  example : p ∨ q ↔ q ∨ p :=
    iff.intro
      (assume hp : p ∨ q,
        show q ∨ p, from or.elim hp (or.intro_right q) (or.intro_left p))
      (assume hq : q ∨ p,
        show p ∨ q, from or.elim hq (or.intro_right p) (or.intro_left q))

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    iff.intro
      (assume h : (p ∧ q) ∧ r,
        show p ∧ (q ∧ r), from
          and.intro
            (and.left (and.left h))
            (and.intro
              (and.right (and.left h))
              (and.right h)))
      (assume h : p ∧ (q ∧ r),
        show (p ∧ q) ∧ r, from
          and.intro
            (and.intro
              (and.left h)
              (and.left (and.right h)))
            (and.right (and.right h)))

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  begin
    split,

    -- (p ∨ q) ∨ r → p ∨ (q ∨ r)
    {
      assume h,

      have f : (p ∨ q) → p ∨ q ∨ r,
      assume pq : (p ∨ q),
      exact
        or.elim
        pq
        (λ hp : p, or.intro_left (q ∨ r) hp)
        (λ hq : q, or.intro_right p (or.intro_left r hq)),

      have g : r → p ∨ q ∨ r,
      assume hr : r,
      exact or.intro_right p (or.intro_right q hr),

      exact or.elim h f g,
    },

    -- p ∨ (q ∨ r) → (p ∨ q) ∨ r
    {
      assume h,

      have f : p → (p ∨ q) ∨ r,
      assume hp,
      exact or.intro_left r (or.intro_left q hp),

      have g : (q ∨ r) → (p ∨ q) ∨ r,
      assume qr,
      exact
        or.elim
        qr
        (λ hq : q, or.intro_left r (or.intro_right p hq))
        (λ hr : r, or.intro_right (p ∨ q) hr),

      exact or.elim h f g,
    },
  end

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  begin
    split,

    {
      assume h,
      
      have f : q → (p ∧ q) ∨ (p ∧ r),
      assume hq : q,
      exact or.intro_left (p ∧ r) (and.intro (and.left h) hq),

      have g : r → (p ∧ q) ∨ (p ∧ r),
      assume hr,
      exact or.intro_right (p ∧ q) (and.intro (and.left h) hr),

      exact or.elim (and.right h) f g,
    },

    {
      assume h,

      have f : p ∧ q → p ∧ (q ∨ r),
      assume pq : p ∧ q,
      exact and.intro (and.left pq) (or.intro_left r (and.right pq)),

      have g : p ∧ r → p ∧ (q ∨ r),
      assume pr : p ∧ r,
      exact and.intro (and.left pr) (or.intro_right q (and.right pr)),

      exact or.elim h f g,
    },
  end

  section
    variable hp : p

    #check and.intro (or.intro_left q hp)
  end
  
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  begin
    split,

    -- p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    {
      assume h,

      have f : p → (p ∨ q) ∧ (p ∨ r),
      assume hp : p,
      exact
        and.intro
          (or.intro_left q hp)
          (or.intro_left r hp),

      have g : q ∧ r → (p ∨ q) ∧ (p ∨ r),
      assume qr,
      exact
        and.intro
          (or.intro_right p (and.left qr))
          (or.intro_right p (and.right qr)),

      exact or.elim h f g,
    },

    -- (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r)
    {
      assume h,
      have hpq : p ∨ q, from and.left h,
      have hpr : p ∨ r, from and.right h,

      have f : p → p ∨ (q ∧ r),
      assume hp,
      exact or.intro_left (q ∧ r) hp,

      have g : q → p ∨ (q ∧ r),
      assume hq,
      exact or.elim hpr f (λ hr : r, or.intro_right p (and.intro hq hr)),

      exact or.elim hpq f g,
    },
  end

  -- other properties
  --
  -- NOTE: Leaving these blank because I think I've got the hang of these kinds
  --       of derivations.
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ false ↔ p := sorry
  example : p ∧ false ↔ false := sorry
  example : ¬(p ↔ ¬p) := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end

-- Exercise 2
--
-- Prove the following identities, replacing the “sorry” placeholders with
-- actual proofs. These require classical reasoning.
section
  open classical

  variables p q r s : Prop

  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry
end

-- Exercise 3
--
-- Prove ¬(p ↔ ¬p) without using classical logic.
section
  variables p : Prop

  example : ¬(p ↔ ¬p) := sorry
end
