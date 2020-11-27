## Exercise 3.29

Show that the following is equivalent to foldR.

    foldRose ∷ (α → List β → β) → Rose α → β
    foldRose f (Node a ts) = f a (mapL (foldRose f) ts)

(a) We define foldRose in terms of foldR/foldF.

We can use the universal property from the next exercise to state:

    foldRose h = foldR f g

    iff

    foldRose h (Node x ts) = f x (foldF f g ts)

where t = Node a ts is any rose tree.

Using the definition of foldRose, this gives us the equation

      h x (mapL (foldRose h) ts) = f x (foldF f g ts)

    ≡   { foldR universal property }

      h x (mapL (foldR f g) ts) = f x (foldF f g ts)

    ≡   { foldF.1 }

      h x (foldF f g ts) = f x (foldF f g ts)

    ≡   { generalizing (foldF f g ts) to xs, η-equivalence }

      h = f

Considering the type signature of foldR, we now have f ∷ α → List β → β,
so γ = List β and g ∷ List β → List β.  So let's consider the
following equation, which we can extract from the previous use of the
foldR universal property:

      foldF f g ts = mapL (foldRose f) ts

    ≡   { foldF.1 }

      g (mapL (foldR f g) ts) = mapL (foldRose f) ts

    ≡   { foldR universal property }

      g (mapL (foldR f g) ts) = mapL (foldR f g) ts

    ≡   { generalizing (mapL (foldR f g) ts) to xs }

      g xs = xs

so we can define g = id.

This gives us the definition:

    foldRose f = foldR f id
