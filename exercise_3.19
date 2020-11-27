## Exercise 3.19

Express predN in terms of foldN; then, show how it can be generalized.

    predN          ∷ Nat → Maybe Nat
    predN Zero     = Nothing
    predN (Succ n) = Just n

Using the universal property of foldN, we have

    predN = foldN z s

    iff

    predN n = case n of
                Zero   → z
                Succ m → s (predN m)

This gives the equations

    predN Zero     = z
    predN (Succ m) = s (predN m)

The solution to the first is immediate: z = Nothing.  For the second
equation, we reason:

      s (predN m) = predN (Succ m)

    ≡   { predN.2 }

      s (predN m) = Just m

We have a problem: we can’t generalize (predN m), because m would occur
free on the right-hand side.  But we can use what we know about the
predecessor function, namely, that Succ (Pred m) = m, to expand the RHS.
We can't use Succ directly, because of the type of predN.

    ≡   { define: predInv ∷ Maybe Nat → Nat }

      s (predN m) = Just (predNInv (predN m))
        where
          predNInv Nothing  = Zero
          predNInv (Just n) = Succ n

    ≡   { generalizing (predN m) to mx }

      s mx = Just (predNInv mx)
        where
          predNInv Nothing  = Zero
          predNInv (Just n) = Succ n

    ≡   { η-equivalence }

      s = Just ∘ predNInv
        where
          predNInv Nothing  = Zero
          predNInv (Just n) = Succ n

The complete definition is then:

    predN = foldN Nothing (Just ∘ predInv)
      where
        predNInv Nothing  = Zero
        predNInv (Just n) = Succ n

TODO: How can we generalize from this?
