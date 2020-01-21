universe u
variables (α β γ : Type u)

-- Exercise 1
--
-- Define the function do_twice, as described in Section 2.4.
def do_twice : (α → α) → α → α :=
  λ f : (α → α), λ x : α, f (f x)

-- Exericse 2
--
-- Define the functions curry and uncurry, as described in Section 2.4.
def curry (f : α × β → γ) : α → β → γ :=
  λ a : α, λ b : β, f (a, b)

def uncurry (f : α → β → γ) : α × β → γ :=
  λ p : α × β, f p.fst p.snd

-- Exercise 3
--
-- Above, we used the example vec α n for vectors of elements of type α of
-- length n. Declare a constant vec_add that could represent a function that
-- adds two vectors of natural numbers of the same length, and a constant
-- vec_reverse that can represent a function that reverses its argument. Use
-- implicit arguments for parameters that can be inferred. Declare some
-- variables and check some expressions involving the constants that you have
-- declared.
constant vec : Type u → ℕ → Type u

constant vec_add : Π {α : Type u}, Π {m n : ℕ}, vec α m → vec α n → vec α (m + n)

constant vec_reverse : Π {α : Type u}, Π {n : ℕ}, vec α n → vec α n

constant vec1 : vec ℕ 4
constant vec2 : vec ℕ 3

section
  variables (vec1 : vec ℕ 4) (vec2 : vec ℕ 5)

  #check vec_add vec1 vec2
  #check vec_add vec2 vec1

  #check vec_reverse vec1
  #check vec_reverse vec2
end

-- Exericse 4
--
-- Similarly, declare a constant matrix so that matrix α m n could represent the
-- type of m by n matrices. Declare some constants to represent functions on
-- this type, such as matrix addition and multiplication, and (using vec)
-- multiplication of a matrix by a vector. Once again, declare some variables
-- and check some expressions involving the constants that you have declared.
constant matrix : Type u → ℕ → ℕ → Type u

constant matrix_add : Π {α : Type u}, Π {m n : ℕ}, matrix α m n → matrix α m n → matrix α m n

constant matrix_mul : Π {α : Type u}, Π {l m n : ℕ}, matrix α l m → matrix α m n → matrix α l m

section
  variables
    (matrix1 : matrix ℕ 2 2)
    (matrix2 : matrix ℕ 3 2)

  #check matrix_add matrix1 matrix1

  -- Expect this to fail:
  -- #check matrix_add matrix1 matrix2

  #check matrix_mul matrix2 matrix1

  -- Expect this to fail:
  -- #check matrix_mul matrix1 matrix2
end
