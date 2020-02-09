--------------
-- Learning --

namespace dfa

  -- Defining a DFA as a tuple of its components
  structure DFA (Q) (Γ) (δ : Q → Γ → Q) (q0 : Q) (F : set Q)

  -- Defining whether a DFA accepts a string
  def arg_accept (Q)
                 (Γ)
                 (δ : Q → Γ → Q)
                 (F : set Q) : Q → list Γ → Prop
    | q list.nil := F q
    | q (list.cons γ l) := arg_accept (δ q γ) l

  def accepts {Q}
              {Γ}
              {δ : Q → Γ → Q}
              {q0 : Q}
              {F : set Q} :  DFA Q Γ δ q0 F → list Γ → Prop :=
    (λ _ l, arg_accept Q Γ δ F q0 l)

  -- A concrete example of a DFA accepting a string.
  section
    inductive Q
      | qstart : Q
      | qlose : Q

    inductive Γ
      | a : Γ
      | b : Γ

    open Q
    open Γ

    def δ : Q → Γ → Q
      | qstart a := qstart
      | qstart b := qlose
      | qlose  _ := qlose

    def q0 := qstart

    def F : set Q
      | qstart := true
      | _      := false

    variable (dfa : DFA Q Γ δ q0 F)

    #reduce accepts dfa [a, a, a]
  end
end dfa
