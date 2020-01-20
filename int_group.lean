namespace hidden

inductive myint : Type
  | zero : myint
  | succ : myint -> myint
  | pred : myint -> myint

open myint

axiom succ_pred_eq (n : myint) :
  succ (pred n) = n

axiom pred_succ_eq (n : myint) :
  pred (succ n) = n

def identity : myint := zero

def inverse : myint -> myint
  | zero := zero
  | (succ n) := pred (inverse n)
  | (pred n) := succ (inverse n)

def add : myint -> myint -> myint
  | m zero := m
  | m (succ n) := succ (add m n)
  | m (pred n) := pred (add m n)

-- Identity properties
lemma add_zero (m : myint) :
  add m zero = m :=
  begin
    rw add,
  end

lemma zero_add (m : myint) :
  add zero m = m :=
  begin
    induction m with d hd d hd,

    -- Base case
    {
      rw add,
    },

    -- Succ case
    {
      rw add,
      rw hd,
    },

    -- Pred case
    {
      rw add,
      rw hd,
    }
  end

-- Associativity
lemma associativity (a b c : myint) :
  add a (add b c) = add (add a b) c :=
  begin
    induction c with d hd d hd,

    -- Base case
    {
      repeat {rw add},
    },

    -- Succ case
    {
      repeat {rw add},
      rw hd,
    },

    -- Pred case
    {
      repeat {rw add},
      rw hd,
    },
  end

-- Intermediate lemmas for inverse
lemma add_succ (m n : myint) :
  add (succ m) n = succ (add m n) :=
  begin
    induction n with d hd d hd,

    -- Base case
    {
      repeat {rw add},
    },

    -- Succ case
    {
      repeat {rw add},
      rw hd,
    },

    -- Pred case
    {
      repeat {rw add},
      rw hd,
      rw [pred_succ_eq, succ_pred_eq],
    },
  end

lemma add_pred (m n : myint) :
  add (pred m) n = pred (add m n) :=
  begin
    induction n with d hd d hd,

    -- Base case
    {
      repeat {rw add},
    },

    -- Succ case
    {
      repeat {rw add},
      rw hd,
      rw [succ_pred_eq, pred_succ_eq],
    },

    -- Pred case
    {
      repeat {rw add},
      rw hd,
    },
  end

-- Inverse properties
lemma add_inverse (n : myint) :
  add n (inverse n) = zero :=
  begin
    induction n with d hd d hd,

    -- Base case
    {
      rw inverse,
      rw add,
    },

    -- Succ case
    {
      rw inverse,
      rw add,
      rw add_succ,
      rw pred_succ_eq,
      rw hd,
    },

    -- Pred case
    {
      rw inverse,
      rw add,
      rw add_pred,
      rw succ_pred_eq,
      rw hd,
    },
  end

lemma inverse_add (n : myint) :
  add (inverse n) n = zero :=
  begin
    induction n with d hd d hd,

    -- Base case
    {
      rw inverse,
      rw add,
    },

    -- Succ case
    {
      rw inverse,
      rw add,
      rw add_pred,
      rw succ_pred_eq,
      rw hd,
    },

    -- Pred case
    {
      rw inverse,
      rw add,
      rw add_succ,
      rw pred_succ_eq,
      rw hd,
    },
  end

end hidden
