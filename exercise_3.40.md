# Exercise 3.40

(a) NTS: For associative f,

    foldL f e (lzw f (Cons x xs) ys) =  f x (foldL f e (lzw f ys xs))

The proof is by induction on list ys and non-empty list xs.

Our assumption is that

    f (f x y) z = f x (f y z)

for all x, y, z.

Case arbitrary xs, ys = Nil:

      foldL f e (lzw f (Cons x xs) Nil)

    =  { lzw.2 }

      foldL f e (Cons x xs)

    =  { foldL.2 }

      f x (foldL f e xs)

    =  { lzw.1 }

      f x (foldL f e (lzw f Nil xs))

which establishes the case.

Case (Cons x (Cons x' xs)), (Cons y ys).  We assume that:

    foldL f e (lzw f (Cons x' xs) ys) =  f x' (foldL f e (lzw f ys xs))

and reason as follows:

      foldL f e (lzw f (Cons x (Cons x' xs)) (Cons y ys))

    =  { lzw.3 }

      foldL f e (Cons (f x y) (lzw f (Cons x' xs) ys))

    =  { foldL.2 }

      f (f x y) (foldL f e (lzw f (Cons x' xs) ys))

    =  { hypothesis }

      f (f x y) (f x' (foldL f e (lzw f ys xs)))

    =  { associativity of f }

      f x (f y (f x' (foldL f e (lzw f ys xs))))

    =  { associativity of f }

      f x (f (f y x') (foldL f e (lzw f ys xs)))

    =  { foldL.2 }

      f x (foldL f e (Cons (f y x') (lzw f ys xs)))

    =  { lzw.3 }

      f x (foldL f e (lzw f (Cons y ys) (Cons x' xs)))

which establishes the case. ∎


(b) Derive

    bff = unfoldL nil first rest
      where
        first (Cons t ts) = root t
        rest (Cons t ts)  = appendL ts (kids t)

as "a simple consequence of the universal property of unfoldL".

We have

    bff = concatL ∘ levelf

By the universal property,

    bff = unfoldL p f g

    iff

    bff xs = if p xs then Nil else Cons (f xs) (bff (g xs))

We know that bff xs = Nil iff xs = Nil, so the solution

    p = nil

is immediate.  We know consider the case nil (Cons x xs) = False:

      bff (Cons x xs) = if nil (Cons x xs)
                          then Nil
                          else Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { nil (Cons x xs) = False, ITE }

      bff (Cons x xs) = Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { bff.1, levelf.1 (unfold version) }

      concatL (unfoldL nil (mapL root) (concatL ∘ mapL kids) (Cons x xs)) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { unfoldL.1, nil (Cons x xs) = False, ITE }

      concatL (Cons (mapL root (Cons x xs))
                    (unfoldL (mapL root) (concatL ∘ mapL kids)
                      (concatL (mapL kids (Cons x xs))))) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { levelf.1 (?) }

      concatL (Cons (mapL root (Cons x xs))
                    (bff (concatL (mapL kids (Cons x xs))))) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { concatL.1, mapL.2 }

      appendL (Cons (root x) (mapL root xs))
              (concatL (bff (concatL (mapL kids (Cons x xs))))) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { appendL.2 }

      Cons (root x)
           (appendL (mapL root xs)
                    (concatL (bff (concatL (mapL kids (Cons x xs)))))) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

    ≡  { define: first (Cons x xs) = root x }

      Cons (first (Cons x xs))
           (appendL (mapL root xs)
                    (concatL (bff (concatL (mapL kids (Cons x xs)))))) =
        Cons (f (Cons x xs)) (bff (g (Cons x xs)))

We’ve derived a solution for f.  Now we try to disentangle the knot
around g.

Maybe this is simpler?

We need solutions for f and g in the equation:

    bff (Cons t ts) = Cons (f (Cons t ts)) (bff (g (Cons t ts)))

We reason:

    concatL (levelf (Cons t ts)) = Cons (f (Cons t ts)) (bff (g (Cons t ts)))

  ≡  { levelf.1, foldF.1 }

    concatL (k (mapL (foldR h k) (Cons t ts))) =
      Cons (f (Cons t ts)) (bff (g (Cons t ts)))
        where
          h x xss = Cons (wrap x) xss
          k       = foldL (lzw appendL) Nil

  ≡  { mapL.2, k def. }

    concatL (foldL (lzw appendL) Nil (Cons (foldR h k t) (mapL (foldR h k) ts))
      = Cons (f (Cons t ts)) (bff (g (Cons t ts)))
        where
          h x xss = Cons (wrap x) xss
          k       = foldL (lzw appendL) Nil

  ≡  { foldL.2 }

    concatL (lzw appendL (foldR h k t)
                         (foldL (lzw appendL) Nil (mapL (foldR h k) ts)))
      = Cons (f (Cons t ts)) (bff (g (Cons t ts)))
        where
          h x xss = Cons (wrap x) xss
          k       = foldL (lzw appendL) Nil
