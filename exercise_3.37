## Exercise 3.37

Use Hughes’s representation of lists as list transformers to derive
alternative versions of levelt' and levelf':

    levelt" ∷ Rose α → List (List α → List α)
    levelf" ∷ Forest α → List (List α → List α)

We can use the abstraction and representation functions defined by
Hughes:

    abst ∷ (List α → List α) → List α
    abst x = x Nil

    rep ∷ List α → (List α → List α)
    rep = appendL

Then, I suppose, we can write some specifications.

    levelt" = mapL rep ∘ levelt
    levelf" = mapL rep ∘ levelf

To calculate levelt", we can use foldR fusion.  We have

    mapL rep ∘ foldR f g = foldR f' g'

if

    g' ∘ mapL (mapL rep) = mapL rep ∘ foldL (lzw appendL) Nil

and

    (f' xs) ∘ mapL rep = mapL rep ∘ Cons (wrap xs),
      for all xs

Let's try to calculate a definition for f'.  We have the type

      f' xs (mapL rep yss) = mapL rep (Cons (wrap xs) yss)

    ≡  { mapL.2 }

      f' xs (mapL rep yss) = Cons (rep (wrap xs)) (mapL rep yss)

    ≡  { generalize (mapL rep yss) to gs }

      f' xs gs = Cons (rep (wrap xs)) gs

which gives us a definition for f'.

Now, g' ∷ List (List (Hughes α)) → List (Hughes α).  We use a case
analysis on the list xss.

Case Nil:

      g' (mapL (mapL rep) Nil) = mapL rep (foldL (lzw appendL) Nil Nil)

    ≡  { mapL.1 twice, foldL.1 }

      g' Nil = Nil

Case (Cons xs xss):

      g' (mapL (mapL rep) (Cons xs xss)) =
        mapL rep (foldL (lzw appendL) Nil (Cons xs xss))

    ≡  { foldL.2 }

      g' (mapL (mapL rep) (Cons xs xss)) =
        mapL rep (lzw appendL xs (foldL (lzw appendL) Nil xss))

    ≡  { theorem: mapL rep (lzw appendL xs ys) =
           lzw appendR (mapL rep xs) (mapL rep ys) }

      g' (mapL (mapL rep) (Cons xs xss)) =
        lzw appendR (mapL rep xs) (mapL rep (foldL (lzw appendL) Nil xss))

    ≡  { hypothesis }

      g' (mapL (mapL rep) (Cons xs xss)) =
        lzw appendR (mapL rep xs) (g' (mapL (mapL rep) xss))

    ≡  { mapL.2 }

      g' (Cons (mapL rep xs) (mapL (mapL rep) xss)) =
        lzw appendR (mapL rep xs) (g' (mapL (mapL rep) xss))

    ≡  { generalize (mapL rep xs) to ks and (mapL (mapL rep) xss) to kss }

      g' (Cons ks kss) = lzw appendR ks (g' kss)

Using the universal property of foldL, it’s easy to see that g' is a
fold:

    g' kss = case kss of
               Nil → Nil
               Cons ks kss → (lzw appendR) ks (g' kss)

So we have

    g' = foldL (lzw appendR) Nil

Putting the definitions of f' and g' together, we have a definition
for levelt" and levelf".

    (levelt", levelf") = (foldR f' g', foldF f' g')
      where
        f' xs = Cons (rep (wrap xs))
        g'    = foldL (lzw appendR) Nil
