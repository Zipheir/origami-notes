## Exercise 3.38

Derive the unfoldL version of levelf using the universal property of
unfoldL.  Then, figure out how to express levelt as an unfold.

Applying the universal property of unfoldL, we have:

    levelf = unfoldL p f g

    iff

    levelf ts = if p ts then Nil else Cons (f ts) (levelf (g ts))

We have the types:

    ts ∷ Forest α                 (given by the type of levelf)
    p  ∷ Forest α → Bool          (infer from ts, unfoldL)
    f  ∷ Forest α → List α        (infer from ts, unfoldL)
    g  ∷ Forest α → Forest α      (infer from ts, unfoldL)

Let's calculate by a case analysis on (p ts).

Case p ts = True:

We know that levelf Nil = Nil and can apply this information immediately.

      if p Nil then Nil else Cons (f Nil) (levelf (g Nil))

    =  { define: p = nil }

      if nil Nil then Nil else Cons (f Nil) (levelf (g Nil))

    =  { nil.1, ITE }

      Nil

    (= levelf Nil)

So we have p = Nil.

From here, it gets really hairy.  TODO.
