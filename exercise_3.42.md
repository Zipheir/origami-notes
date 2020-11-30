# Exercise 3.42

(a) Define

    takeL, dropL ∷ Nat → List α → List α

as a list unfold and natural fold, respectively.

First, takeL.  The usual definition is

    takeL Zero xs              = Nil
    takeL (Succ n) Nil         = Nil
    takeL (Succ n) (Cons x xs) = Cons x (takeL n xs)

To write this as an unfold, we need access to both the List and Nat
arguments.  We define an uncurried version of takeL, which gives us
the type of our unfold:

    takeLu ∷ (Nat, List α) → List α

    ((Nat, List α) → Bool) → ((Nat, List α) → α) →
      ((Nat, List α) → (Nat, List α)) → (Nat, List α) → List α

Using the universal property of unfoldL,

    takeLu = unfoldL p f g

    iff

    takeLu b = if p b
                 then Nil
                 else Cons (f b) (takeLu (g b))

We calculate by case analysis on b ∷ (Nat, List α).

Since takeLu (n, xs) is Nil when (1) n = Zero or (2) xs = Nil, we
immediately define

    p (n, xs) = isZero n || nil xs

We now consider the case (Succ n, Cons x xs):

      takeLu (Succ n, Cons x xs) =
        if p (Succ n, Cons x xs)
          then Nil
          else Cons (f (Succ n, Cons x xs))
                    (takeLu (g (Succ n, Cons x xs)))

    ≡  { takeLu.3, p def., ITE }

      Cons x (takeLu (n, xs)) = Cons (f (Succ n, Cons x xs))
                                  (takeLu (g (Succ n, Cons x xs)))

We extract the equations for f and g, which are basically the
definitions we’re looking for:

    f (Succ n, Cons x xs) = x
    g (Succ n, Cons x xs) = (n, xs)

The full definition is then

    takeL = curry takeLu

    takeLu = unfoldL p f g
      where
        p (n, xs)             = isZero n || nil xs
        f (n, Cons x xs)      = x
        g (Succ n, Cons x xs) = (n, xs)

*  *  *

Here’s the usual def. of dropL:

    dropL Zero xs              = xs
    dropL (Succ n) Nil         = Nil
    dropL (Succ n) (Cons x xs) = dropL n xs

Using the universal property of foldN:

    dropL = foldN z s

    iff

    dropL n = case n of
                Zero   → z
                Succ m → s (h m)

We have the types:

    dropL n, foldN z s n ∷ List α → List α
    z                    ∷ List α → List α
    s                    ∷ (List α → List α) → (List α → List α)

We include the argument list xs.  Case n = Zero:

      (foldN z s Zero) xs = dropL Zero xs

    ≡  { dropL.1 }

      (foldN z s Zero) xs = xs

    ≡  { foldN.1 }

      z xs = xs

We define z = id.

For the case (Succ n), let’s ignore the “short list” case for a minute.

      (foldN z s (Succ n)) (Cons x xs) = dropL (Succ n) (Cons x xs)

    ≡  { foldN.2, dropL.3 }

      (s (foldN z s n)) (Cons x xs) = dropL n xs

    ≡  { tail.1 }

      (s (foldN z s n)) (Cons x xs) = dropL n (tail (Cons x xs))

    ≡  { hypothesis }

      (s (foldN z s n)) (Cons x xs) = (foldN z s n) (tail (Cons x xs))

    ≡  { generalize (foldN z s n) to f, rewrite as composition }

      (s f) (Cons x xs) = (f ∘ tail) (Cons x xs)

Now, assume the input list is Nil.

      (foldN z s (Succ n)) Nil = dropL (Succ n) Nil

    ≡  { foldN.2, dropL.2 }

      (s (foldN z s n)) Nil = Nil

    ≡  { hypothesis, dropL.1 & 2 }

      (s (dropL n)) Nil = dropL n Nil

    ≡  { generalize (dropL n) to f }

      (s f) Nil = f Nil

    ≡  { id/∘ right identity }

      (s f) Nil = (f ∘ id) Nil

So we have the equations

    (s f) Nil         = (f ∘ id) Nil
    (s f) (Cons x xs) = (f ∘ tail) (Cons x xs)

Rewriting s as (λg → g ∘ h), we replace these with

    (f ∘ h) Nil         = (f ∘ id) Nil
    (f ∘ h) (Cons x xs) = (f ∘ tail) (Cons x xs)

We can see that s is a total version of ‘tail’:

    s = ttail

    ttail Nil         = Nil
    ttail (Cons x xs) = xs

So our final definition is

    dropL n = foldN id (λf → ttail ∘ f) n

This completes the synthesis.


(b) Define unravel:

    unravel ∷ Nat → List α → List α

Gibbons is pretty vague about this function, but it’s an inverse to
ravel; ‘unravel h’ splits a list into the subsequences composed of
every hth element of the list.  We need a “pre-inverse” to concat:

    sublists ∷ Nat → List α → List (List α)
    sublists n = unfoldL nil (takeL n) (dropL n)

And then we have

    unravel n = trans ∘ sublists n
