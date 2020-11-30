## Exercise 3.28

Define fix f = f (f (...)).

I don't see how we can define this, as written, due to the
self-application of f; isn't the type infinite?  TODO: Look at
Meijer & Hutton, _Bananas In Space_ and try to figure this out.


# 3.4 Origami With Trees: Traversals

We’re going to be working with rose trees:

    data Rose a   = Node a (Forest a)
    type Forest a = List (Rose a)

The folds for trees and forests, like the data types, are mutually
recursive:

    foldR ∷ (α → γ → β) → (List β → γ) → Rose α → β
    foldR f g (Node a ts) = f a (foldF f g ts)

    foldF ∷ (α → γ → β) → (List β → γ) → Forest α → γ
    foldF f g ts = g (mapL (foldR f g) ts)
