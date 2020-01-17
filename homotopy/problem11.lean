def compose (A B C : Type) (g : B -> C) (f : A -> B) :=
    fun x : A, g (f x)

lemma associative_compose
    (A B C D : Type)
    (f : A -> B)
    (g : B -> C)
    (h : C -> D) :
    compose A C D h (compose A B C g f) =
    compose A B D (compose B C D h g) f :=
    begin
        rw [compose, compose, compose, compose],
    end

