## Exercise 3.16

Define a single-argument foldN' and define each version in terms of
the other.

By ‘single-argument’ is meant that the z and s arguments of foldN are
unified; foldN' will still need a Nat argument, of course.  We state
the type, by analogy with foldL':

    foldN′ ∷ (Maybe α → α) → Nat → α

and try to reason from the following specification:

    foldN′ t = foldN z s

The calculation proceeds by induction on the Nat argument.

Case Zero:

      foldN′ f Zero = foldN z s Zero

    ≡   { foldN.1 }

      foldN′ f Zero = z

    ≡   { define: f Nothing = z }

      foldN′ f Zero = f Nothing

which gives us the first equation for foldN′.

Case Succ n:

      foldN′ f (Succ n) = foldN z s (Succ n)

    ≡   { foldN.2 }

      foldN′ f (Succ n) = s (foldN z s n)

    ≡   { hypothesis }

      foldN′ f (Succ n) = s (foldN′ f n)

    ≡   { define: f (Just m) = s m }

      foldN′ f (Succ n) = f (Just (foldN′ f n))

which gives us the second equation.  This completes the calculation.

    foldN′ ∷ (Maybe α → α) → Nat → α
    foldN′ f Zero     = f Nothing
    foldN′ f (Succ n) = f (Just (foldN′ f n))

Defining foldN in terms of foldN' is just a matter of collecting the
helper definitions in the above calculation:

    foldN z s = foldN' f
      where
        f Nothing  = z
        f (Just m) = s m

To define foldN' in terms of foldN, we have the specification

    foldN' f = foldN z s

and calculate as follows:

      foldN z s Zero = foldN' f Zero

    ≡   { foldN.1, foldN'.1 }

      z = f Nothing

which gives a value for z.

Proceeding,

      foldN z s (Succ n) = foldN' f (Succ n)

    ≡   { foldN.2, foldN'.2 }

      s (foldN z s n) = f (Just (foldN' f n))

    ≡   { hypothesis }

      s (foldN z s n) = f (Just (foldN z s n))

    ≡   { generalize (foldN z s n) to m }

      s m = f (Just m)

which gives a definition for s.  We have:

    foldN' f = foldN (f ∘ Just) (f Nothing)
