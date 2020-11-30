# Exercise 3.4

Define insert₁ as a fold:

    insert₁      ∷ Ord α ⇒ α → List α → (List α, List α)
    insert₁ y xs = (xs, insert y xs)

Using the universal property of foldL, we have

    (insert₁ y) = foldL f e

iff

    (insert₁ y) xs = case xs of
                       Nil       → e
                       Cons z zs → f z ((insert₁ y) zs)

So we have the equations

    insert₁ y Nil         = e
    insert₁ y (Cons x xs) = f x (insert₁ y xs)

The first is easy.  By the definition above, we have

    insert₁ y Nil = (Nil, insert y Nil)
                  = (Nil, wrap y)

So given y : α, we have e = (Nil, wrap y).

In the second equation, we need to solve for
f ∷ α → (List α, List α) → (List α, List α).

      insert₁ y (Cons x xs) = f x (insert₁ y xs)

    ≡   { insert₁ def. }

      (Cons x xs, insert y (Cons x xs)) = f x (xs, insert y xs)

Consider the case y ≥ x.  We reason as follows:

      (Cons x xs, insert y (Cons x xs)) = f x (xs, insert y xs)

    ≡   { insert.2 }

      (Cons x xs, Cons x (insert y xs)) = f x (xs, insert y xs)

    ≡   { generalizing (insert y xs) to ys }

      (Cons x xs, Cons x ys) = f x (xs, ys)

So far, we have

    f x (xs, ys) = if y < x then ... else (Cons x xs, Cons x ys)

(where y is in the enclosing function’s scope.)

Now, the case y < x:

      insert₁ y (Cons x xs) = f x (xs, insert y xs)

    ≡   { insert₁ def. }

      (Cons x xs, insert y (Cons x xs)) = f x (xs, insert y xs)

    ≡   { generalizing (insert y xs) to ys }

      (Cons x xs, insert y (Cons x xs)) = f x (xs, ys)

    ≡   { insert.2 }

      (Cons x xs, Cons y (Cons x xs)) = f x (xs, ys)

This eliminates all free variables other than y.  Putting together
the two cases, and the earlier equation for e, we have:

    insert₁ y zs = foldL f (Nil, wrap y)
      where
        f x (xs, ys) = if y < x
                         then (Cons x xs, Cons y (Cons x xs))
                         else (Cons x xs, Cons x ys)

This completes the calculation of insert₁.
