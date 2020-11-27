# Exercise 3.13

‘insert’, (way) above can be defined as an unfold.  Do it.

    insert ∷ Ord α ⇒ α → List α → List α
    insert y Nil = wrap y
    insert y (Cons x xs)
      | y < x     = Cons y (Cons x xs)
      | otherwise = Cons x (insert y xs)

The hint is that the first (List α) element of the “state” tuple is
the list into which to insert the maybe-wrapped second element.  Once
the element has been inserted, later unfold steps get Nothing.

As the exercises suggests, it’s a lot easier to do this with unfoldL′.
The hint gives us

    insert y = unfoldL′ f u

where

    f ∷ ((List α, Maybe α) → Maybe (α, (List α, Maybe α)))
    u ∷ (List α, Maybe α)

We have:

    insert' y xs = unfoldL′ ins (xs, Just y)

    ins (Nil, Nothing)       = Nothing
    ins (Nil, Just x)        = Just (x, (Nil, Nothing))
    ins (Cons z zs, Nothing) = Just (z, (zs, Nothing))
    ins (Cons z zs, Just x)
      | x < z                = Just (x, (Cons z zs, Nothing))
      | otherwise            = Just (z, (zs, Just x))

This definition is a bit unwieldy!  In particular, it seems a little
inelegant to not be able to generate the tail (wrap x) in the second
equation for ins.  (Scheme's unfold, with its tail-gen procedure, can
do this.)

But I’m pretty sure it’s correct.  We need to prove this.

    insert y xs = insert' y xs

The proof of the above proposition is by induction on the list xs.

Case Nil:

      insert' y Nil

    =   { insert'.1 }

      unfoldL' ins (Nil, Just y)

    =   { ins.2, unfoldL'.1 }

      case Just (y, (Nil, Nothing)) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL′ ins v)

    =   { case, pattern matching }

      Cons y (unfoldL′ ins (Nil, Nothing))

    =   { unfoldL'.1 }

      Cons y (case ins (Nil, Nothing) of
                Nothing → Nil
                Just (x, v) → …)

    =   { ins.1 }

      Cons y (case Nothing of
                Nothing → Nil
                Just (x, v) → …)

    =   { case, pattern matching }

      Cons y Nil

    =   { wrap.1 }

      wrap y

    =   { insert.1 }

      insert y Nil

which establishes the case.

For the inductive step, we need the following lemma.

Lemma: unfoldL' ins (xs, Nothing) = xs

The proof is by structural induction on the list xs.

Case Nil:

      unfoldL' ins (Nil, Nothing)

    =   { unfoldL'.1 }

      case ins (Nil, Nothing) of
        Nothing → Nil
        Just (x, v) → …

    =   { ins.1 }

      case Nothing of
        Nothing → Nil
        Just (x, v) → …

    =   { case }

      Nil

which establishes the case.

Case Cons y ys:

      unfoldL' ins (Cons y ys, Nothing)

    =   { unfoldL'.1 }

      case ins (Cons y ys, Nothing) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

    =   { ins.3 }

      case Just (z, (zs, Nothing)) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

    =   { case, pattern matching }

      Cons z (unfoldL' ins (zs, Nothing))

    =   { hypothesis }

      Cons z zs

which establishes the case. ∎

Case Cons z zs:

      insert' y (Cons z zs)

    =   { insert'.1 }

      unfoldL' ins (Cons z zs, Just y)

    =   { unfoldL'.1 }

      case ins (Cons z zs, Just y) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

We have two subcases to consider.

Subcase y < z:

    =   { ins.4 }

      case Just (y, (Cons z zs, Nothing)) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

    =   { case, pattern matching }

      Cons y (unfoldL' ins (Cons z zs, Nothing))

    =   { lemma }

      Cons y (Cons z zs)

    =   { insert.2 }

      insert y (Cons z zs)

Subcase y ≥ z:

      case ins (Cons z zs, Just y) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

    =   { ins.5 }

      case Just (z, (zs, Just y)) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL' ins v)

    =   { case, pattern matching }

      Cons z (unfoldL' ins (zs, Just y))

    =   { insert'.1 }

      Cons z (insert' y zs)

    =   { hypothesis }

      Cons z (insert y zs)

    =   { insert.2 }

      insert y (Cons z zs)

which establishes the case. ∎

(Writing this proof revealed some mistakes in the def. of insert'!)
