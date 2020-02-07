import init.data.fin
import init.data.list
import init.data.nat.basic

open nat

namespace hidden
  universe u

  -- Defining a list
  inductive list (α : Type u) : Type (u + 1)
    | nil  : list
    | cons : α → list → list

  namespace list
    def length {α : Type u} : list α → ℕ
      | (nil α)    := 0
      | (cons _ l) := 1 + length l

    def nth_le {α : Type u} : Π (l : list α) (n : ℕ), n < l.length → α
      | (nil α)    n       h := absurd h (not_lt_zero n)
      | (cons a l) 0       h := a
      | (cons a l) (n + 1) h :=
        nth_le
          l
          n
          begin
            rw length at h,
            rw add_comm 1 (length l) at h,
            repeat {rw add_one_eq_succ at h},
            exact lt_of_succ_lt_succ h,
          end
  end list

  -- Defining the fin type
  structure fin (n : ℕ) :=
    (val : ℕ)
    (is_lt : val < n)

  -- Defining a vector type, which is a list with a given length.
  def vector (α : Type u) (n : ℕ) := { l : list α // l.length = n }

  -- Gets an item from a vector, so long as it's within the range of the index.
  def get {α : Type u} {n : ℕ} : Π (v : vector α n), fin n → α
    | ⟨ l, h ⟩ i :=
      l.nth_le i.1
      begin
        rw h,
        exact i.2,
      end
end hidden
