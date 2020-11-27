## Exercise 3.10

‘deleteL’ is a paramorphism.  Redefine it using ‘paraL’.

We seek a solution to the following for all finite lists xs:

    deleteL y = paraL f e

Going by the type of paraL, we have the type signatures

    f ∷ α → (List α, List α) → List α
    e ∷ List α

First, the case Nil.

      paraL f e Nil = deleteL y Nil

    ≡  { deleteL.1, paraL.1 }

      e = Nil

which is our first solution.  Continuing, the non-empty case gives
us two subcases.

Case (Cons x xs), subcase y == x:

      paraL f e (Cons x xs) = deleteL y (Cons x xs)

    ≡   { deleteL.2 }

      paraL f e (Cons x xs) = xs

    ≡   { paraL.2 }

      f x (xs, paraL f e xs) = xs

    ≡   { generalizing (paraL f e xs) to ys }

      f x (xs, ys) = xs

Case (Cons x xs), subcase y ≠ x:

      paraL f e (Cons x xs) = deleteL y (Cons x xs)

    ≡   { deleteL.2 }

      paraL f e (Cons x xs) = Cons x (deleteL y xs)

    ≡   { paraL.2 }

      f x (xs, paraL f e xs) = Cons x (deleteL y xs)

    ≡   { hypothesis: paraL f e xs = deleteL y xs, generalize to ys }

      f x (xs, ys) = Cons x ys

which gives the remaining solution for f.  Putting it all together,
we have:

    deleteL y = paraL f Nil
      where f x (xs, ys) = if y == x
                             then xs
                             else Cons x ys

This completes the synthesis.
