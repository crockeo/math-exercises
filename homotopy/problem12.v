Definition p1 (A B : Type) : (A * B) -> A := fun p => fst p.
Definition p2 (A B : Type) : (A * B) -> B := fun p => snd p.

Section Book_12.
    Variable A : Type.
    Variable B : Type.

    Definition recAX (C : Type) : (A -> B -> C) -> (A * B) -> C :=
        fun g p => g (p1 A B p) (p2 A B p).

    Proposition p1_equality : p1 A B = recAX A (fun a b => a).
    Proof.
        reflexivity.
    Defined.

    Proposition p2_equality : p2 A B = recAX B (fun a b => b).
    Proof.
        reflexivity.
    Defined.
End Book_12.
