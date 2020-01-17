-- Base-level definition of naturals
inductive mynat : Type
    | zero : mynat
    | succ : mynat -> mynat

open mynat

-------------------------------------------------------------------------------
--                                Addition                                   --
-------------------------------------------------------------------------------

-- Addition on naturals
def add : mynat -> mynat -> mynat
    | m zero     := m
    | m (succ n) := succ (add m n)

-------------------------
-- Prerequisite Proofs --

-- Proving that zero is the additive identity
lemma mynat_add_zero (n : mynat) : (add n zero) = n :=
    begin
        rw add,
    end

-- Proving that zero is the additive identity, even in reverse order.
lemma mynat_zero_add (n : mynat) :
    (add zero n) = n :=
    begin
        induction n with d hd,

        -- Base case
        rw mynat_add_zero,

        -- Inductive case
        rw add,
        rw hd,
    end

lemma mynat_add_succ (x y : mynat) :
    succ (add x y) = add (succ x) y :=
    begin
        induction y with d hd,

        -- Base case
        rw [mynat_add_zero, mynat_add_zero],

        -- Inductive case
        rw add,
        rw hd,
        rw add,
    end

-------------------------
-- Commutativity Proof --
lemma add_commutativity (x y : mynat) :
    add x y = add y x :=
    begin
        induction y with d hd,

        -- Base case
        rw mynat_add_zero,
        rw mynat_zero_add,

        -- Inductive case
        rw add,
        rw <- mynat_add_succ,
        rw hd,
    end

-------------------------
-- Associativity Proof --
lemma add_associativity (x y z : mynat) :
    add x (add y z) = add (add x y) z :=
    begin
        induction x with d hd,

        -- Base case
        rw [mynat_zero_add, mynat_zero_add],

        -- Inductive case
        rw <- mynat_add_succ,
        rw hd,
        rw <- mynat_add_succ,
        rw <- mynat_add_succ,
    end
