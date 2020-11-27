## Exercise 3.17

The universal property for foldN is presumably:

    h = foldN z s

    iff

    h n = case n of
            Zero   → z
            Succ m → s (h m)

for all h : Nat → α.  I’d like to know how we can prove that this
is indeed a universal property.

To derive a fusion law, we need a solution to the equation:

    f ∘ foldN z s = foldN z' s'

Using the above universal property, we know that this holds iff:

    (f ∘ foldN z s) Zero     = z'
    (f ∘ foldN z s) (Succ n) = s' ((f ∘ foldN z s) n)

The solution to the first equation is almost immediate:

      z' = f (foldN z s Zero)

    ≡   { foldN.1 }

      z' = f z

For the second equation, we reason as follows:

      s' (f (foldN z s n)) = f (foldN z s (Succ n))

    ≡   { foldN.2 }

      s' (f (foldN z s n)) = f (s (foldN z s n))

    ≡   { generalizing (foldN z s n) to x }

      s' (f x) = f (s x)

    ≡   { rewrite as a composition, η-equivalence }

      s' ∘ f = f ∘ s

which gives a constraint for s'.

So we have the following fusion law:

    f ∘ foldN z s = foldN z' s'

    if

    (f z = z') ∧ (s' ∘ f = f ∘ s)
