# Exercise 3.11

Define ‘delmin’ as a paramorphism.

Again, we seek a solution to the following for lists xs:

    paraL f e = delmin

This gives us some (slightly gnarly) types:

    e ∷ Maybe (α, List α)
    f ∷ α → (List α, Maybe (α, List α)) → Maybe (α, List α)

...

It might be helpful to define a fold equivalent to a tupled function
like this:

    -- xs ≠ Nil
    delmin′ xs = (xs, (minimumL xs, deleteL (minimumL xs) xs))

Let’s try this.

...

    delmin′ = foldL1 f
      where
        f y (ys, (x, zs))
          | y ≤ x     = (Cons y ys, (y, ys))
          | otherwise = (Cons y ys, (x, Cons y zs))

Back to the main challenge.

The solution for the first equation,

    paraL f e Nil = delmin′ Nil

is immediate: e = Nothing.

For the second equation, we consider the cases Cons x Nil and
Cons x (Cons x′ Nil).

Case Cons x Nil:

      paraL f e (Cons x Nil) = delmin (Cons x Nil)

    ≡   { paraL.2, delmin.2 }

      f x (Nil, paraL f e Nil) = Just (minimumL (Cons x Nil),
        deleteL (minimumL (Cons x Nil)) (Cons x Nil))

    ≡   { evaluating minimumL on a singleton list }

      f x (Nil, paraL f e Nil) = Just (x, deleteL x (Cons x Nil))

    ≡   { deleteL.2, generalizing (paraL f e Nil) to m }

      f x (Nil, m) = Just (x, Nil)

This gives us "the real base case".

Case Cons x (Cons x′ xs).  We use the induction hypothesis

    paraL f e (Cons x′ xs) = delmin (Cons x′ xs)

The calculation proceeds:

      paraL f e (Cons x (Cons x′ xs)) = delmin (Cons x (Cons x′ xs))

    ≡   { paraL.2, delmin.2 }

      f x (Cons x′ xs, paraL f e (Cons x′ xs)) =
        Just (minimumL (Cons x (Cons x′ xs)),
          deleteL (minimumL (Cons x (Cons x′ xs))) (Cons x (Cons x′ xs)))

    ≡   { induction hypothesis }

      f x (Cons x′ xs, delmin (Cons x′ xs)) =
        Just (minimumL (Cons x (Cons x′ xs)),
          deleteL (minimumL (Cons x (Cons x′ xs))) (Cons x (Cons x′ xs)))

    ≡   { delmin.2 }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (minimumL (Cons x (Cons x′ xs)),
          deleteL (minimumL (Cons x (Cons x′ xs))) (Cons x (Cons x′ xs)))

        where y = minimumL (Cons x′ xs)

We will need an easy lemma.

Lemma 1: If x : α and x > minimumL xs, then

    minimumL (Cons x xs) = minimumL xs

Proof:

      minimumL (Cons x xs)
    =   { minimumL.1 }
      foldL min x xs
    =   { foldL.2, twice }
      min x (minimumL xs)
    =   { assumption }
      minimumL xs
∎

Lemma 2: If x ≤ minimumL xs, then

    minimumL (Cons x xs) = x

The proof is identical to the above, with min x (minimumL xs) = x.


We have two cases to consider.

Case x > y:

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (minimumL (Cons x (Cons x′ xs)),
          deleteL (minimumL (Cons x (Cons x′ xs))) (Cons x (Cons x′ xs)))

        where y = minimumL (Cons x′ xs)

    ≡   { case statement, lemma 1 }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (y, deleteL y (Cons x (Cons x′ xs)))

        where y = minimumL (Cons x′ xs)

    ≡   { deleteL.2, x ≠ y }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (y, Cons x (deleteL y (Cons x′ xs)))

        where y = minimumL (Cons x′ xs)

    ≡   { generalizing (deleteL y (Cons x′ xs)) to ys }

      f x (Cons x′ xs, Just (y, ys)) = Just (y, Cons x ys)

        where y = minimumL (Cons x′ xs)

    ≡   { generalizing y }

      f x (Cons x′ xs, Just (y, ys)) = Just (y, Cons x ys)

which gives us a solution for the case.  So far,

Case x ≤ y:

    ≡   { generalizing y }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (minimumL (Cons x (Cons x′ xs)),
          deleteL (minimumL (Cons x (Cons x′ xs))) (Cons x (Cons x′ xs)))

    ≡   { lemma 2 }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (x, deleteL x (Cons x (Cons x′ xs)))

    ≡   { deleteL.2 }

      f x (Cons x′ xs, Just (y, deleteL y (Cons x′ xs))) =
        Just (x, (Cons x′ xs))

    ≡   { generalizing (deleteL y (Cons x′ xs)) to ys }

      f x (Cons x′ xs, Just (y, ys)) = Just (x, (Cons x′ xs))

which gives the solution to the remaining case.

    delmin = paraL f Nothing
      where
        f x (Nil, m) = Just (x, Nil)
        f x (Cons x′ xs, Just (y, ys))
          | x > y     = Just (y, Cons x ys)
          | otherwise = Just (x, Cons x′ xs)

This completes the synthesis.  Whew!
