# Exercise 3.8

(a) Define foldL′ in terms of foldL.

We can use the universal property for this.  We have:

    foldL′ f = foldL g e

if and only if

    foldL′ f xs = case xs of
                    Nil       → e
                    Cons y ys → g y (foldL′ f ys)

which gives us two equations,

    foldL′ f Nil         = e
    foldL′ f (Cons y ys) = g y (foldL′ f ys)

The solution to the first is immediate: e = f Nothing.  For the
second, we reason:

      foldL′ f (Cons y ys) = g y (foldL′ f ys)

    ≡  { foldL′.2 }

      f (Just (y, foldL′ f ys)) = g y (foldL′ f ys)

    ≡  { generalizing (foldL′ f ys) ∷ β to z }

      f (Just (y, z)) = g y z

Having solved for e and g, we can apply the universal property:

    foldL′ f = foldL g (f Nothing)
      where
        g y z = f (Just (y, z))


(b) Define foldL in terms of foldL′.

We're looking for a definition of the form

    foldL f e xs = foldL′ g xs

which holds for all lists xs.  To obtain this, we only need a
definition of g ∷ (Maybe (α, β) → β).  We reason by synthesis on
the list xs.

Case Nil:

      foldL f e Nil = foldL′ g Nil

    ≡  { foldL.1, foldL′.1 }

      e = g Nothing

which gives the first equation for g.

Case (Cons x xs): We use the induction hypothesis

    foldL f e xs = foldL′ g xs,

reasoning as follows:

      foldL′ g (Cons x xs) = foldL f e xs

    ≡  { foldL.2, foldL′.1 }

      g (Just (x, foldL′ g xs)) = f x (foldL f e xs)

    ≡  { hypothesis }

      g (Just (x, foldL′ g xs)) = f x (foldL′ g xs)

    ≡  { generalizing (foldL′ g xs) to ys }

      g (Just (x, ys)) = f x ys

which gives the second equation for g.  We have:

    foldL f e = foldL′ g
      where
        g Nothing        = e
        g (Just (x, ys)) = f x ys

This completes the synthesis.
