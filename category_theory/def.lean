universes v u v₂ u₂

-- TODO:
--   * Define a monoidal category
--   * Specialize monoid on the endofunctor
--   * ???
--   * Profit

namespace hidden

-- Defining a class of things that have homomorphisms.
class has_hom (obj : Type u) : Type (max u (v + 1)) :=
  (hom : obj → obj → Type v)

infixr ` ⟶ ` : 10 := has_hom.hom

-- Defining the backend for the category definition.
class category_struct (obj : Type u)
  extends has_hom.{v} obj : Type (max u (v + 1)) :=
    -- For any object, there exists the identity morphism on that object.
    (id : Π x : obj, x ⟶ x)

    -- For any two morphisms, we can construct the composition of those
    -- morphisms.
    (comp : Π {x y z : obj}, (x ⟶ y) → (y ⟶ z) → (x ⟶ z))

notation `𝟙` := category_struct.id
infixr ` ≫ ` : 80 := category_struct.comp

-- Defining the properties of a category
class category (obj : Type u)
  extends category_struct.{v} obj : Type (max u (v + 1)) :=
    -- Composition has left and right identity, with exactly the identity
    -- morphism on any value.
    (id_comp : ∀ {x y : obj} (f : hom x y), ((𝟙 x) ≫ f) = f)
    (comp_id : ∀ {x y : obj} (f : hom x y), (f ≫ (𝟙 y)) = f)

    -- Composition is associative
    (assoc :
      ∀ {w x y z : obj}
        (f : hom w x)
        (g : hom x y)
        (h : hom y z),
          (f ≫ g) ≫ h = f ≫ (g ≫ h))

-- Defining a functor over categories
structure functor (C : Type u)
                  [category.{v} C]
                  (D : Type u₂)
                  [category.{v₂} D] : Type (max u v u₂ v₂) :=
  -- Map objects to objects
  (obj : C → D)

  -- Map morphisms to morphisms
  (map : Π {x y : C}, (x ⟶ y) → ((obj x) ⟶ (obj y)))

  -- Map maintains id
  (map_id : ∀ (x : C), map (𝟙 x) = 𝟙 (obj x))

  -- Map maintains composition
  (map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
    map (f ≫ g) = (map f) ≫ (map g))

-- Specializing functor to a type where we have only
def endofunctor (C : Type u) [category.{v} C] := functor C C

-- Defining a monoid
structure monoid (C : Type u)
                 [category.{v} C] : Type (max u v) :=
  (id : C)
  (mul : C → C → C)

  (id_mul : ∀ (c : C), mul id c = c)
  (mul_id : ∀ (c : C), mul c id = c)

-- Defining a monoidal category
-- class monoidal_category (obj : Type u)
--   extends category.{v} obj : Type (max u (v + 1)) :=

-- TODO: Is this all for naught? What do I hope to learn from this? Enough
--       information to return, now triumphant, to a Zulip channel? God said,
--       Thou shalt not research out of spite, and we followed His command, for
--       His word is eternal.

end hidden
