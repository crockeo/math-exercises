mport data.set.basic
import data.nat.basic
import logic.basic

open set
open nat

universe u

-- Exercise 1
-- Exercise 2
-- Exercise 3
--   I know I shouldn't, but I'm skipping these because I want to learn how to
--   prove things I can't just show using a normal programming language.

-- Exercise 4
section
    lemma union_empty (α : Type u) (A : set α) :
        A ∪ ∅ = A :=
        begin
            rw union_def,
            ext a,
            rw mem_set_of_eq,
            rw mem_empty_eq,
            rw or_false,
        end

    lemma intersection_empty (α : Type u) (A : set α) :
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
    lemma union_comm (α : Type u) (A B : set α) :
        A ∪ B = B ∪ A :=
        begin
            repeat {rw union_def},
            ext,
            repeat {rw mem_set_of_eq},
            rw or_comm,
        end

    lemma intersection_comm (α : Type u) (A B : set α) :
        A ∩ B = B ∩ A :=
        begin
            repeat {rw inter_def},
            ext,
            repeat {rw mem_set_of_eq},
            rw and_comm,
        end
end

-- Exercise 6
section
    lemma union_distrib (α : Type u) (A B C : set α) :
        A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
        begin
            repeat {rw inter_def},
            repeat {rw union_def},

            ext a,

            repeat {rw mem_set_of_eq},
            rw or_and_distrib_left,
        end
end

-- Exercise 7
section
    lemma inter_distrib (α : Type u) (A B C : set α) :
        A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
        begin
            repeat {rw inter_def},
            repeat {rw union_def},

            ext a,

            repeat {rw mem_set_of_eq},
            rw and_or_distrib_left,
        end
end

-- Exercise 8
-- TODO: this is horrible
section
    lemma subset_inter (α : Type u) (A B : set α) :
        (A ⊆ B) ↔ (A ∩ B = A) :=
        begin
            split,

            {
                assume h,
                ext,
                rw inter_def,
                rw mem_set_of_eq,

                split,

                -- Proving x ∈ A ∧ x ∈ B → x ∈ A
                assume h',
                cases h' with hl hr,
                apply hl,

                -- Proving x ∈ A → x ∈ A ∧ x ∈ B
                assume hl,
                rw subset_def at h,
                have hr : x ∈ B, from (h x) hl,
                apply and.intro hl hr,
            },

            {
                assume h,
                rw <- h,
                assume x : α,
                rw [inter_def, mem_set_of_eq],
                assume h',
                cases h' with hl hr,
                apply hr,
            },
        end
end

-- Exercise 9
-- TODO: Syntax for complement?
-- section
--     lemma complement_inter (α : Type u) (A B : set α) :
--         (A ∩ B)
-- end

-- Exercise 10
section
    lemma union_minus_identity (α : Type u) (A B : set α) :
        (A ∪ B) = (A ∩ B) ∪ (A \ B) ∪ (B \ A) :=
        begin
            sorry,
        end
end

-- Exercise 11
-- section
--     lemma right_times_dist (α : Type u) (A B C : set α) :
--         (A ∪ B) × C = (A × C) ∪ (B × C) :=
--         begin
--             sorry,
--         end
-- end

-- Exercise 12
section
    lemma cap_minus_empty (α : Type u) (A B : set α) :
        (A ∩ B) \ B = ∅ :=
        begin
            ext,
            rw diff_eq,
            rw inter_assoc,
            rw inter_compl_self,
            rw inter_empty,
        end
end

-- Exercise 13
section
    lemma union_minus_identity' (α : Type u) (A B : set α) :
        (A ∪ B) \ B = A \ B :=
        begin
            ext,

            rw diff_eq,
            rw inter_comm,
            rw inter_distrib,
            rw [inter_comm (-B) A, inter_comm (-B) B],
            rw inter_compl_self,
            rw set.union_empty,
            rw <- diff_eq,
        end
end

-- Exercise 14

-- Exercise 15

-- Exercise 16

-- Exercise 17

-- Exercise 18

-- Exercise 19

-- Exercise 20

-- Exercise 21

-- Exercise 22

-- Exercise 23

-- Exercise 24

-- Exercise 25

-- Exercise 26

-- Exercise 27

-- Exercise 28

-- Exercise 29

