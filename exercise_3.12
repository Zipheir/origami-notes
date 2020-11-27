## Exercise 3.12

Define a version of bubble,

    bubbleL ∷ Ord α ⇒ List α → List α,

which returns the list (Cons x xs), where Just (x, xs) = bubble ys
for all lists ys.

We can write the following equations, which establish the isomorphism
between the types Maybe (α, List α) and List α:

    Nothing      = Nil
    Just (x, xs) = Cons x xs

Then, it's just a matter of using these equations to substitute lists
for maybes in ‘bubble’:

    bubble ∷ Ord α ⇒ List α → List α
    bubble = foldL step Nil
      where
        step x Nil = wrap x
        step x (Cons y ys)
          | x < y      = Cons x (Cons y ys)
          | otherwise  = Cons y (Cons x ys)

We use ‘wrap’, which is more idiomatic than Cons x Nil.
