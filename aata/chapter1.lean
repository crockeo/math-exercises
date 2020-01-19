import data.set.basic
import data.nat.basic
import logic.basic

open set
open nat

-- Exercise 1
-- Exercise 2
-- Exercise 3
--   I know I shouldn't, but I'm skipping these because I want to learn how to
--   prove things I can't just show using a normal programming language.

-- Exercise 4
section
    lemma union_empty (α : Type) (A : set α) :
        A ∪ ∅ = A :=
        begin
            rw union_def,
            ext a,
            rw mem_set_of_eq,
            rw mem_empty_eq,
            rw or_false,
        end

    lemma intersection_empty (α : Type) (A : set α) :
        A ∩ ∅ = ∅ :=
        begin
            rw inter_def,
            ext a,
            rw mem_set_of_eq,
            repeat {rw mem_empty_eq},
            rw and_false,
        end
end

-- Exercise 5
section
    lemma union_comm (α : Type) (A B : set α) :
        A ∪ B = B ∪ A :=
        begin
            repeat {rw union_def},
            ext,
            repeat {rw mem_set_of_eq},
            rw or_comm,
        end

    lemma intersection_comm (α : Type) (A B : set α) :
        A ∩ B = B ∩ A :=
        begin
            repeat {rw inter_def},
            ext,
            repeat {rw mem_set_of_eq},
            rw and_comm,
        end
end
