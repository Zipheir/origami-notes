## Exercise 3.25

Deforest the following:

    hyloN' :: (Maybe a -> a) -> (a -> Maybe a) -> a -> a
    hyloN' f g = foldN' f . unfoldN' g

We'd like to calculate a new definition for hyloN' that does not use
foldN' or unfoldN'.  We'll try to proceed by case analysis on g in the
expression:

    hyloN' f g x = case g x of ...

Case g x = Nothing:

      hyloN' f g x = foldN' f (unfoldN' g x)

    ≡   { unfoldN'.1 }

      hyloN' f g x = foldN' f (case g x of
                                 Nothing -> Zero
                                 Just y  -> Succ (unfoldN' g y))

    ≡   { g x = Nothing, case }

      hyloN' f g x = foldN' f Zero

    ≡   { foldN'.1 }

      hyloN' f g x = f Nothing

which gives a value for this case:

    hyloN' f g x = case g x of
                     Nothing -> f Nothing
                     -- ...

This looks slightly redundant.

Case g x = Just y:

      hyloN' f g x = foldN' f (unfoldN' g x)

    ≡   { unfoldN'.1 }

      hyloN' f g x = foldN' f (case g x of
                                 Nothing -> Zero
                                 Just y  -> Succ (unfoldN' g y))

    ≡   { g x = Just y, case, pattern matching }

      hyloN' f g x = foldN' f (Succ (unfoldN' g y))
        [where y = fromJust (g x)]

    ≡   { foldN'.1 }

      hyloN' f g x = f (Just (foldN' f (unfoldN' g y)))
        [where y = fromJust (g x)]

    ≡   { unapply, rewrite as composition }

      hyloN' f g x = f (Just ((foldN' f ∘ unfoldN' g) y))
        [where y = fromJust (g x)]

    ≡   { specification }

      hyloN' f g x = f (Just (hyloN' f g y))
        [where y = fromJust (g x)]

which gives a solution for this case.

    hyloN' f g x = case g x of
                     Nothing -> f Nothing
                     Just y  -> f (Just (hyloN' f g y))

This completes the calculation.
