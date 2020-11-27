## Exercise 3.18

Express addN, mulN, powN in terms of foldN.

Each function has the type

    f ∷ Nat → Nat → Nat

addN is really familiar, but it's good practice to calculate it.

Using the universal property, we have

    addN m = foldN z s

    iff

    addN m n = case n of
                 Zero → z
                 Succ p → s (addN m p)

So we have the equations

    addN m Zero     = z
    addN m (Succ n) = s (addN m n)

Since m + Zero = m for all natural numbers m, we have z = m.  And, by
associativity, we have

    addN m (Succ n) = Succ (addN m n)

and thus

    s = Succ

The completed definition:

    addN   ∷ Nat → Nat → Nat
    addN m = foldN m Succ

Again using the universal property, we get similar equations for mulN:

    mulN m Zero     = z
    mulN m (Succ n) = s (mulN m n)

We use the definition of multiplication to state:

    mulN m Zero     = Zero = z

    mulN m (Succ n) = addN m (mulN m n),
                    =   { define s = addN m }
                      s (mulN m n)

giving us the following definition:

    mulN   ∷ Nat → Nat → Nat
    mulN m = foldN Zero (addN m)

Finally, powN (powN b n = b ^ n).

    powN b Zero     = z
    powN b (Succ n) = s (powN b n)

We have:

    powN b Zero = (Succ Zero) = z

    powN b (Succ n) = mulN b (powN b n)
                    =   { define s = mulN b }
                      s (powN b n)

which gives the fold:

    powN   ∷ Nat → Nat → Nat
    powN b = foldN (Succ Zero) (mulN b)
