# Exercise 3.2

I lost my calculations for mapL, but here it is, a classic of
fold universality:

    mapL ∷ (α → β) → List α → List β
    mapL f = foldL (Cons ∘ f) Nil

We look at the flipped version of appendL, defined by

    appendL' ys Nil         = ys
    appendL' ys (Cons x xs) = Cons x (appendL' ys xs)

(appendL' ys xs is equivalent to appendL xs ys.)

Using the universal property of foldL, we need to solve the following
for e and f:

    (appendL' ys) Nil         = e
    (appendL' ys) (Cons z zs) = f z ((appendL' ys) zs)

The first is immediate: e = ys.  The second:

    (appendL' ys) (Cons z zs) = f z ((appendL' ys) zs)
  =   { appendL'.2, unapply appendL' }
    Cons z (appendL' ys zs) = f z (appendL' ys zs)

and thus f = Cons.  So we have:

    (appendL' ys) = foldL Cons ys

We can now get back the original form,

    appendL xs ys = foldL Cons ys xs,

which completes the derivation.


Lastly, concatL is defined by:

    concatL ∷ List (List α) → List α
    concatL Nil           = Nil
    concatL (Cons xs xss) = appendL xs (concatL xss)

Using the universal property of foldL, we need to solve the following
for e and f:

    concatL Nil           = e
    concatL (Cons xs xss) = f xs (concatL xss)

By a straightforward application of the equations for concatL, we have
e = Nil and f = appendL, so:

    concatL = foldL appendL Nil
