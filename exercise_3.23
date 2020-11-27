## Exercise 3.23

divN ∷ Nat -> Nat -> Nat as an instance of unfoldN or unfoldN'.

We'll assume that division by zero causes an exception to be raised.
It's possible to return a Maybe value, but this is a needless
complication, since there's never any useful information to be had
from a divide-by-zero.

We have a further issue, though--we'll need to make use of subN, which
returns a Maybe value.

To express this as an unfold, we interpret integer division as repeated
subtraction of the divisor b from the dividend a, terminating when the
dividend is zero.  That is, we will unfold on a, which means reversing
the order of the arguments.

Using the universal property of unfoldN, we have

    divN b = unfoldN p f

    iff

    divN b x = if p x then Zero else Succ (divN b (f x))

Since we need to use subN, x ∷ Maybe Nat.

Using a = bq + r and ignoring r, we know that q = Zero when a = Zero
or a < b.  So we define

    p ∷ Maybe Nat -> Bool
    p (Just Zero)     = True    -- unneeded, see below
    p (Just (Succ a)) = lessN (Succ a) b

But we've excluded the (undefined) case b = Zero, so, if a = Zero, then
we can conclude a < b.  So the first case can be dropped.

We have:

    divN b (Just Zero) = Zero

For the case p x = False, we have a ≥ b.  So:

    divN b a = Succ (divN b (subN a b)),  (*)

that is, the quotient of a and b is one plus the quotient of (a - b)
and b.

      divN b (Just (Succ a)) = if p (Just (Succ a))
                                 then Zero
                                 else Succ (divN b (f (Just (Succ a))))

    ≡   { p (Just (Succ a)) = False, ITE }

      divN b (Just (Succ a)) = Succ (divN b (f (Just (Succ a))))

    ≡   { (*) }

      Succ (divN b (subN (fromJust (Just (Succ a))) b))
        = Succ (divN b (f (Just (Succ a))))

    ≡   { abstraction }

      Succ (divN b ((λma → subN (fromJust ma) b) (Just (Succ a))))
        = Succ (divN b (f (Just (Succ a))))

    ≡   { generalizing (Just (Succ a)) to mx }

      Succ (divN b ((λma → subN (fromJust ma) b) mx)) = Succ (divN b (f mx))

which gives us a solution for f.

    f ∷ Maybe Nat -> Maybe Nat
    f Nothing  = Nothing  -- can't happen
    f (Just a) = subN a b

where b is in the enclosing function's scope.

So the final definition (using an as-pattern for clarity) is:

    divN a b@(Succ x) = unfoldN p f (Just a)
      where
        p (Just m) = lessN m b
        f (Just c) = subN c b
