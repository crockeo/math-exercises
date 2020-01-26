-- Exercise 1
--
-- Prove these equivalences:
section
  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  begin
    split,

    {
      assume h,
      split,
      
      {
        assume hx,
        exact and.left (h hx),
      },

      {
        assume hx,
        exact and.right (h hx),
      },
    },

    {
      assume h,
      assume hx,

      exact and.intro (and.left h hx) (and.right h hx),
    },
  end
  
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  begin
    assume hpq,
    assume hp,
    assume x,

    exact hpq x (hp x),
  end
  
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  begin
    have f : (∀ x, p x) → ∀ x, p x ∨ q x,
    {
      assume hpx,
      assume hx,

      exact or.intro_left (q hx) (hpx hx),
    },

    have g : (∀ x, q x) → ∀ x, p x ∨ q x,
    {
      assume hqx,
      assume hx,

      exact or.intro_right (p hx) (hqx hx),
    },

    assume h,
    exact or.elim h f g,

    -- NOTE: Not derivable because there exist situations in which
    --       (∀ x, p x ∨ q x) is true, but (∀ x, p x) ∨ (∀ x, q x) is not. The
    --       former can mix truthiness between the two, but the latter requires
    --       that p must hold for all x, or q must hold for all x.
  end
end

-- Exercise 2
--
-- It is often possible to bring a component of a formula outside a universal
-- quantifier, when it does not depend on the quantified variable. Try proving
-- these (one direction of the second of these requires classical logic):
section
  universe u
  variables (α : Type u) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
  begin
    assume ha,
    split,

    assume har,
    exact har ha,

    assume hr,
    assume haa,
    exact hr,
  end

  variable x : α

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  begin
    split,

    -- hphx : p hx = evidence of the predicate p holding on an element of x
    -- p hx : Prop = a property that may or may not be true of hx

    {
      assume h,

      have pos : r → (∀ x, p x) ∨ r,
      {
        assume hr,
        exact or.inr hr,
      },

      have neg : ¬r → (∀ x, p x) ∨ r,
      {
        assume hnr,

        apply or.inl,
        assume hx,

        exact or.elim (h hx) id (λ hr, absurd hr hnr),
      },

      exact classical.by_cases pos neg,
    },

    {
      assume h,
      assume hx,

      exact
        or.elim
        h
        (λ hl, or.intro_left r (hl hx))
        (λ hr, or.intro_right (p hx) hr),
    },
  end
  
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  begin
    split,

    {
      assume h,
      assume hr,
      assume ha,
      exact (h ha) hr,
    },

    {
      assume h,
      assume ha,
      assume hr,
      exact (h hr) ha,
    },
  end
end

-- Exercise 3
--
-- Consider the “barber paradox,” that is, the claim that in a certain town
-- there is a (male) barber that shaves all and only the men who do not shave
-- themselves. Prove that this is a contradiction:
section
  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)
  variable (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
  begin
    have hiff : (shaves barber barber) ↔ ¬(shaves barber barber), from h barber,

    have f : shaves barber barber → false,
    {
      assume hf,
      exact (hiff.mp hf) hf,
    },

    have g : ¬shaves barber barber → false,
    {
      assume hg,
      exact f (hiff.mpr hg),
    },

    exact classical.by_cases f g,
  end
end


-- Exercise 4
--
-- Below, we have put definitions of divides and even in a special namespace to
-- avoid conflicts with definitions in the library. The instance declaration
-- makes it possible to use the notation m | n for divides m n. Don’t worry
-- about how it works; you will learn about that later.
namespace hidden
  def divides (m n : ℕ) : Prop := ∃ k, m * k = n

  instance : has_dvd nat := ⟨divides⟩

  def even (n : ℕ) : Prop := 2 ∣ n -- You can enter the '∣' character by typing \mid

  section
  variables m n : ℕ

  #check m ∣ n
  #check m^n
  #check even (m^n +3)
  end
end hidden

-- Remember that, without any parameters, an expression of type Prop is just an
-- assertion. Fill in the definitions of prime and Fermat_prime below, and
-- construct the given assertion. For example, you can say that there are
-- infinitely many primes by asserting that for every natural number n, there is
-- a prime number greater than n. Goldbach’s weak conjecture states that every
-- odd number greater than 5 is the sum of three primes. Look up the definition
-- of a Fermat prime or any of the other statements, if necessary.
section
  def prime (n : ℕ) : Prop :=
    ¬∃m: ℕ, m < n ∧ hidden.divides m n

  def infinitely_many_primes : Prop :=
    ∀x : ℕ, ∃y : ℕ, y > x ∧ prime y

  def Fermat_prime (n : ℕ) : Prop :=
    ∃k : ℕ, n = 2^(2 ^ k) + 1

  def infinitely_many_Fermat_primes : Prop :=
    ∀x : ℕ, ∃y : ℕ, y > x ∧ Fermat_prime y

  def goldbach_conjecture : Prop :=
    ∀x : ℕ, x > 2 → ∃y z : ℕ, x = y + z ∧ prime y ∧ prime z

  def Goldbach's_weak_conjecture : Prop :=
    ∀x : ℕ, ¬hidden.even x ∧ x > 5 → ∃a b c : ℕ, x = a + b + c ∧ prime a ∧ prime b ∧ prime c

  def Fermat's_last_theorem : Prop :=
    ¬∃a b c n : ℕ, n > 2 ∧ a^n = b^n + c^n
end

-- Exercise 5
--
-- Prove as many of the identities listed in Section 4.4 as you can.
section
  open classical

  variables (α : Type) (p q : α → Prop)
  variable a : α
  variable r : Prop

  include a

  example : (∃ x : α, r) → r :=
  begin
    assume h,

    have hq : (∀a : α, r → r),
    assume a,
    assume hr,
    exact hr,

    exact exists.elim h hq,
  end
  
  example : r → (∃ x : α, r) :=
  begin
    assume hr,

    exact exists.intro a hr
  end
  
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  begin
    split,

    {
      assume h,

      have hq : ∀(a : α), p a ∧ r → (∃(x : α), p x) ∧ r,
      {
        assume ha,
        assume conj,

        apply and.intro,
        exact exists.intro ha (and.left conj),
        exact and.right conj,
      },
      
      exact exists.elim h hq,
    },

    {
      assume h,
      have hl, from and.left h,
      have hr, from and.right h,

      have hq : ∀(a : α), p a → (∃x : α, p x ∧ r),
      {
        assume ha,
        assume h',
        apply exists.intro,

        exact and.intro h' hr,
      },

      exact exists.elim hl hq,
    },
  end

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hw⟩ :=
    ⟨w, hw.right, hw.left⟩
  end
  
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  begin
    split,

    {
      assume h,

      have f : Π a : α, p a → ∃ (x : α), p x,
      exact exists.intro,

      have g : Π a : α, q a → ∃ (x : α), q x,
      exact exists.intro,

      apply exists.elim h,
      assume ha,
      assume hor,

      exact
        or.elim
        hor
        (λ hpa, or.inl (f ha hpa))
        (λ hqa, or.inr (g ha hqa)),
    },

    {
      assume hor,

      have f : (∃ (x : α), p x) → ∃ (x : α), p x ∨ q x,
      assume hex,
      exact (
        match hex with ⟨ha, hpx⟩ :=
          ⟨ha, or.inl hpx⟩
        end
      ),

      have g : (∃ (x : α), q x) → ∃ (x : α), p x ∨ q x,
      assume hex,
      exact (
        match hex with ⟨ha, hqx⟩ :=
          ⟨ha, or.inr hqx⟩
        end
      ),

      exact or.elim hor f g,
    },
  end

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  begin
    split,

    {
      assume hfa,
      assume hex,

      have f : (∀ (a : α), (λ (x : α), ¬p x) a → false),
      assume a,
      assume hnpa,
      exact hnpa (hfa a),

      exact exists.elim hex f,
    },

    {
      assume hne, 
      assume a,

      apply by_contradiction,
      assume hnpa,

      have he : ∃x : α, ¬p x,
      exact exists.intro a hnpa,

      exact hne he,
    },
  end

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  begin
    split,

    {
      assume hex,
      assume hfa,

      have f : (∀ (a : α), (λ (x : α), p x) a → false),
      assume ha,
      assume hpa,
      exact (hfa ha) hpa,

      exact exists.elim hex f,
    },

    {
      assume hnfa,
      apply by_contradiction,
      assume hnex,

      have hfa : ∀(x : α), ¬p x,
      assume ha,
      assume hpa,
      exact hnex (exists.intro ha hpa),

      exact hnfa hfa,
    },
  end
  
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  begin
    split,

    {
      assume hnex,
      assume ha,
      assume hpa,

      have hex : ∃(x : α), p x,
      exact exists.intro ha hpa,

      exact hnex hex,
    },

    {
      assume hfa,
      assume hex,

      have f : (∀ x : α, (λ a : α, p x) a → false),
      assume ha,
      assume hpa,
      exact (hfa ha) hpa,

      exact exists.elim hex f,
    },
  end
  
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  begin
    split,

    {
      assume hnfa,
      apply by_contradiction,
      assume hnex,

      have hfa : ∀ (x : α), p x,
      assume ha,
      apply by_contradiction,
      assume hpnha,
      exact hnex ⟨ha, hpnha⟩,

      exact hnfa hfa,
    },

    {
      assume hex,
      assume hfa,

      exact (
        match hex with ⟨ha, hnpa⟩ :=
          hnpa (hfa ha)
        end
      ),
    },
  end

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  begin
    split,

    {
      assume hfa,
      assume hex,

      have f : (∀ (x : α), (λ (y : α), p y) x → r),
      assume ha,
      assume hpa,
      exact (hfa ha) hpa,

      exact exists.elim hex f,
    },

    {
      assume h,
      assume ha,
      assume hpa,

      exact h (exists.intro ha hpa),
    },
  end
  
  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  begin
    split,

    {
      assume hex,
      assume hfa,

      have f : (∀ (a : α), (λ (x : α), p x → r) a → r),
      assume ha,
      assume hpar,
      apply hpar,
      exact hfa ha,
      
      exact exists.elim hex f,
    },

    {
      assume h,

      eapply by_cases,

      assume hfa : ∀ (x : α), p x,
      exact ⟨a, (λ hpa, h hfa)⟩,

      assume hnfa,
      have hnex : ∃ (x : α), ¬p x,
      {
        apply by_contradiction,
        assume hnex,
        have hfa : ∀ (x : α), p x,
        {
          assume ha,
          apply by_contradiction,
          assume hnpa,
          exact hnex ⟨ha, hnpa⟩,
        },
        exact hnfa hfa,
      },

      exact (
        match hnex with ⟨x, hnpx⟩ :=
          ⟨x, (λ hpx : p x, absurd hpx hnpx)⟩
        end
      ),
    },
  end
  
  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  begin
    split,

    {
      assume hex,
      assume hr,

      have f : (∀ (a : α), (λ (x : α), r → p x) a → (∃ y : α, p  y)),
      assume ha,
      assume hrpha,
      exact exists.intro ha (hrpha hr),

      exact exists.elim hex f,
    },

    {
      assume h,

      eapply by_cases,

      assume hr : r,
      exact (
        match h hr with ⟨ha, hpa⟩ :=
          ⟨ha, (λ hr' : r, hpa)⟩
        end
      ),

      assume hnr : ¬r,
      exact ⟨a, (λ hr : r, absurd hr hnr)⟩,
    },
  end
end

-- Exercise 6
--
-- Give a calculational proof of the theorem log_mul below.
section
  variables (real : Type) [ordered_ring real]
  variables (log exp : real → real)
  variable  log_exp_eq : ∀ x, log (exp x) = x
  variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
  variable  exp_pos    : ∀ x, exp x > 0
  variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

  -- this ensures the assumptions are available in tactic proofs
  include log_exp_eq exp_log_eq exp_pos exp_add

  example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

  example (y : real) (h : y > 0)  : exp (log y) = y :=
  exp_log_eq h

  theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
    begin
      rw <- exp_log_eq hx,
      rw <- exp_log_eq hy,
      rw <- exp_add,
      repeat {rw log_exp_eq},
    end
end

-- Exericse 7
--
-- Prove the theorem below, using only the ring properties of ℤ enumerated in
-- Section 4.2 and the theorem sub_self.
section
  #check sub_self

  example (x : ℤ) : x * 0 = 0 :=
  begin
    -- NOTE: Is this supposed to be harder? I think that mul_zero is a property
    --       of rings.
    rw mul_zero,
  end
end
