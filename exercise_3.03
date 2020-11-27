# Exercise 3.3

As a corollary of the fusion law, we need to prove the *map
fusion law*:

    foldL f e ∘ map g = foldL (f ∘ g) e

Proof:

We know from the above that map is a fold:

    foldL f e ∘ map g = foldL f e ∘ foldL (Cons ∘ g) Nil

To use fusion, we need to simplify the following:

    [1]  ((foldL f e) ((Cons ∘ g) a b)) = f′ a ((foldL f e) b)
    [2]  (foldL f e) Nil                = e′

[2] is pretty much immediate by the definition of foldL: e′ = e.
For [1], we reason as follows:

    ((foldL f e) ((Cons ∘ g) a b)) = f′ a ((foldL f e) b)

  ≡   { applying Cons ∘ g and unapplying foldL }

    foldL f e (Cons (g a) b) = f′ a (foldL f e b)

  ≡   { foldL.2 }

    f (g a) (foldL f e b) = f′ a (foldL f e b)

  ≡   { eliminating the common term }

    f (g a) = f′ a

  ≡   { rewriting as a composition and eliminating the common term }

    f ∘ g = f′

We now have solutions to the required equations, so we can apply
fusion.  We have:

    foldL f e ∘ foldL (Cons ∘ g) Nil = foldL (f ∘ g) e

  ≡ foldL f e ∘ map g = foldL (f ∘ g) e,

as required. ∎
