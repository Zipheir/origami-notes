## Exercise 3.32

Write ‘lzw’ as an unfold.

First, it’s worth noting that zipWith is very easy to define as an
unfold:

    zw f = unfoldL p g h
      where
        p (xs, ys) = null xs || null ys
        g          = uncurry f ∘ both head
        h          = both tail

    zipWith f = curry (zw f)

with ‘both’ being the function-product combinator:

    both ∷ (α → β) → (α, α) → (β, β)
    both f (x, y) = (f x, f y)

With lzw, though, things are different.  We will work with an uncurried
version, lzw′.

Using the universal property of unfoldL, we have:

    lzw′ f = unfoldL p g h

    iff

    lzw′ f x = if p x then Nil else Cons (g x) (zw f (h x))

We have the following types:

    p ∷ (List α, List α) -> Bool
    g ∷ (List α, List α) -> α
    h ∷ (List α, List α) -> (List α, List α)

A difficulty arises immediately: Nil is only the value of
(lzw′ f (xs, ys)) when xs and ys are both Nil--a case we will never
reach if the lists are of unequal length.

    p (xs, ys) = null xs && null ys

This looks less than promising.  If (p x) is false, we reason:

      lzw′ f z = if p z then Nil else Cons (g z) (zw f (h z))

    ≡   { ITE }

      lzw′ f z = Cons (g z) (zw f (h z))

Now we should have a case analysis, using the equations for lzw′.
Again, it seems like we have a problem: only lzw.3 has a right-hand
side of the form Cons y ys.  But we may be able to remedy this by
rewriting the first two equations so that the patterns are disjoint:

    lzw' f (Nil, Nil)       = Nil                                  (lzw'.1)
    lzw′ f (Nil, Cons y ys) = Cons y ys                             (lzw'.2)
    lzw′ f (Cons x xs, Nil) = Cons x xs                             (lzw'.3)
    lzw′ f (Cons x xs, Cons y ys) = Cons (f x y) (lzw' f (xs, ys))  (lzw'.4)

Now we try again to calculate.

Case z = (Nil, Cons y ys):

      Cons (g (Nil, Cons y ys)) (zw f (h (Nil, Cons y ys))) =
        lzw′ f (Nil, Cons y ys)

    ≡   { lzw′.1 }

      Cons (g (Nil, Cons y ys)) (zw f (h (Nil, Cons y ys))) =
        Cons y ys

    ≡   { define: g (Nil, Cons y ys) = y }

      Cons y (zw f (h (Nil, Cons y ys))) = Cons y ys

We appear to be stuck, since we can’t eliminate the (zw ...) term on
the left-hand side.

We can fare much better if we instead define lzw as an apomorphism.
(But see below, after this exercise.)

We seek a definition of the form

    lzw' f = apoL' g

We proceed by case analysis on the tuple argument p.  The first case
is easy.

Case p = (Nil, Nil):

      apoL' g (Nil, Nil) = lzw' f (Nil, Nil)

    ≡   { apoL'.1, lwz'.1 }

      (case g (Nil, Nil) of
        Nothing -> Nil
        ...)                 = Nil

So we define

    g (Nil, nil) = Nothing

Case p = (Cons x xs, Nil):

      apoL' g (Cons x xs, Nil) = lzw' f (Cons x xs, Nil)

    ≡   { apoL'.1, lzw'.2 }

      (case g (Cons x xs, Nil) of
        Nothing -> Nil
        Just (z, Left v) -> Cons z (apoL' g v)
        Just (z, Right zs) -> Cons z zs)       = Cons x xs

We define:

    g (Cons x xs, Nil) = Cons x xs

The case p = (Nil, Cons y ys) is almost identical, and gives us

    g (Nil, Cons y ys) = Cons y ys

Case p = (Cons x xs, Cons y ys).  We assume as an induction hypothesis
that lzw' f (xs, ys) = apoL' g (xs, ys).

      apoL' g (Cons x xs, Cons y ys) = lzw' f (Cons x xs, Cons y ys)

    ≡   { apoL'.1, lzw'.4 }

      (case g (Cons x xs, Cons y ys) of
        Nothing -> Nil
        Just (z, Left v) -> Cons z (apoL' g v)
        Just (z, Right zs) -> Cons z zs)       = Cons (f x y)
                                                   (lzw' f (xs, ys))

    ≡   { hypothesis }

      (case g (Cons x xs, Cons y ys) of
        Nothing -> Nil
        Just (z, Left v) -> Cons z (apoL' g v)
        Just (z, Right zs) -> Cons z zs)       = Cons (f x y) (apoL' g (xs, ys))

We define:

    g (Cons x xs, Cons y ys) = Just (f x y, Left (xs, ys))

Putting together our definition, we have:

    lzw' f = apoL' g
      where
        g (Nil, Nil)             = Nothing
        g (Cons x xs, Nil)       = Cons x xs
        g (Nil, Cons y ys)       = Cons y ys
        g (Cons x xs, Cons y ys) = Just (f x y, Left (xs, ys))

And, of course,

    lzw f = curry (lzw f)

*  *  *

Actually, defining the apomorphism version of lzw is the subject of
exercise 3.33!  So there must be a way to define lzw as an unfold.

And here it is.  Gibbons gives us a hint--it’s inefficient because the
longer of the two lists must be reconstructed.

    lzwu f = unfoldL' g
      where
        g (Nil, Nil)             = Nothing
        g (Cons x xs, Nil)       = Just (x, (xs, Nil))
        g (Nil, Cons y ys)       = Just (y, (Nil, ys))
        g (Cons x xs, Cons y ys) = Just (f x y, (xs, ys))

We will prove that this definition is equivalent to the directly
recursive definition by induction on the input list-pair.

Case (Nil, Nil):

      lzwu f (Nil, Nil)

    =   { lzwu.1 }

      unfoldL' g (Nil, Nil)

    =   { unfoldL'.1 }

      case g (Nil, Nil) of
        Nothing -> Nil
        -- ...

    =   { lzwu.g.1, pattern matching, case }

      Nil

    =   { lzw'.1 }

      lzw' f (Nil, Nil)

which establishes the case.

Case (Cons x xs, Nil).  We use the following induction hypothesis:

    lzwu f (xs, Nil) = lzw' f (xs, Nil),

reasoning as follows:

      lzwu f (Cons x xs, Nil)
    = unfoldL' g (Cons x xs, Nil)

    =   { unfoldL'.1 }

      case g (Cons x xs, Nil) of
        Nothing     → Nil
        Just (y, v) → Cons y (unfoldL′ g v)

    =   { lzwu.g.2, case, pattern-matching }

      Cons x (unfoldL' f (xs, Nil))

    =   { hypothesis }

      Cons x (lzw' f (xs, Nil))

    =   { lzw'.1 }

      Cons x xs

    =   { lzw'.1 }

      lzw' f (Cons x xs, Nil)

which establishes the case.

The case (Nil, Cons y ys) is almost identical.

Case (Cons x xs, Cons y ys).  Again we use the usual hypothesis.

      lzwu f (Cons x xs, Cons y ys)
    = unfoldL' g (Cons x xs, Cons y ys)

    =   { unfoldL'.1 }

      case g (Cons x xs, Cons y ys) of
        Nothing     → Nil
        Just (z, v) → Cons z (unfoldL′ g v)

    =   { lzwu.g.4, case, pattern-matching }

      Cons (f x y) (unfoldL' g (xs, ys))

    =   { lzwu.1, hypothesis }

      Cons (f x y) (lzw' f (xs, ys))

    =   { lzw'.3 }

      lzw' f (Cons x xs, Cons y ys)

which establishes the case. ∎
