Definition compose {A B C} (g : B -> C) (f : A -> B) :=
  fun x : A => g (f x).

Theorem Associative_Compose :
  forall (A B C D : Type)
    (f : A -> B)
    (g : B -> C)
    (h : C -> D),
      compose h (compose g f) = compose (compose h g) f.

Proof.
  reflexivity.
Defined.
