------------------
-- Random Notes --

--
-- 7.1. Enumerated Types
--
namespace s71
  inductive weekday : Type
    | sunday : weekday
    | monday : weekday
    | tuesday : weekday
    | wednesday : weekday
    | thursday : weekday
    | friday : weekday
    | saturday : weekday

  namespace weekday
    def next (d : weekday) : weekday :=
      weekday.cases_on d
        monday
        tuesday
        wednesday
        thursday
        friday
        saturday
        sunday

    def previous (d : weekday) : weekday :=
      weekday.cases_on d
        saturday
        sunday
        monday
        tuesday
        wednesday
        thursday
        friday

    theorem next_previous (d : weekday) : next (previous d) = d :=
    begin
      apply weekday.cases_on d;
      refl,
    end

    theorem previous_next (d : weekday) : previous (next d) = d :=
    begin
      apply weekday.cases_on d;
      refl,
    end
  end weekday
end s71

--
-- 7.2. Constructors with Arguments
--
namespace s72
  universes u v

  inductive prod (α : Type u) (β : Type v)
    | mk : α → β → prod


  namespace prod
    def fst {α : Type u} {β : Type v} (p : prod α β) : α :=
      prod.rec_on p (λa b, a)

    def snd {α : Type u} {β : Type v} (p : prod α β) : β :=
      prod.rec_on p (λa b, b)

    section
      variables (α : Type u) (β : Type v) (p : prod α β)
      variables (a : α) (b : β)

      #reduce mk a b
      #reduce fst (mk a b)
      #reduce snd (mk a b)
    end
  end prod

  -- Defining the necessary conditions for a group as a structure.
  --
  -- Now how would one actually use this definition?
  universe t

  structure Group :=
    (carrier : Type t)
    (ident : carrier)

    (inverse : carrier → carrier)
    (mul : carrier → carrier → carrier)

    (ident_mul_eq : ∀ a : carrier, mul ident a = a)
    (mul_ident_eq : ∀ a : carrier, mul a ident = a)

    (inverse_mul_eq_ident : ∀ a : carrier, mul (inverse a) a = ident)
    (mul_inverse_eq_ident : ∀ a : carrier, mul a (inverse a) = ident)

    (mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c))
end s72

---------------
-- Exercises --

-- Exercise 1
--
-- Try defining other operations on the natural numbers, such as multiplication,
-- the predecessor function (with pred 0 = 0), truncated subtraction (with
-- n - m = 0 when m is greater than or equal to n), and exponentiation. Then try
-- proving some of their basic properties, building on the theorems we have
-- already proved.
--
-- Since many of these are already defined in Lean’s core library, you should
-- work within a namespace named hide, or something like that, in order to avoid
-- name clashes.
namespace hidden
  variables (x y : ℕ)

  -- Defining our operations
  def add (x y : ℕ) : ℕ :=
    nat.rec_on
      x
      y
      (λ _ add_x_y, nat.succ add_x_y)

  def mul (x y : ℕ) : ℕ :=
    nat.rec_on
      x
      0
      (λ _ mul_x_y, add mul_x_y y)

  def pred (n : ℕ) : ℕ :=
    nat.rec_on
      n
      0
      (λ n pred_n, n)

  def sub (x y : ℕ) : ℕ :=
    nat.rec_on
      y
      x
      (λ n sub_x_y, pred sub_x_y)

  -- TODO: Define infix operators

  -- Defining some theorems. Skipping most of them because I did them in NN Game
  theorem add_sub_inverse : ∀ (x y : ℕ), x + y - y = x :=
    begin
      intros x y,

      induction y with d hd,

      {
        rw add_zero,
        -- rw sub_zero,
        sorry,
      },

      {
        sorry,
      },
    end
end hidden

-- TODO

-- Exericse 2
--
-- Define some operations on lists, like a length function or the reverse
-- function. Prove some properties, such as the following:
--
-- length (s ++ t) = length s + length t
--
-- length (reverse t) = length t
--
-- reverse (reverse t) = t

-- TODO

-- Exericse 3
--
-- Define an inductive data type consisting of terms built up from the following
-- constructors:
--
-- const n, a constant denoting the natural number n
--
-- var n, a variable, numbered n
--
-- plus s t, denoting the sum of s and t
--
-- times s t, denoting the product of s and t
--
-- Recursively define a function that evaluates any such term with respect to an
-- assignment of values to the variables.

-- Exercise 4
--
-- Similarly, define the type of propositional formulas, as well as functions on
-- the type of such formulas: an evaluation function, functions that measure the
-- complexity of a formula, and a function that substitutes another formula for
-- a given variable.

-- TODO

-- Exercise 5
--
-- Simulate the mutual inductive definition of even and odd described in Section 7.9 with an ordinary inductive type, using an index to encode the choice between them in the target type.

-- TODO
