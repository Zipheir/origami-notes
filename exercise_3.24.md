## Exercise 3.24

Define logN ∷ Nat -> Nat -> Nat as an instance of unfoldN.

We want to compute logN b n = log to the base b of n, rounded down to
the nearest natural.  We can compute this by successive divisions of
n by b, using the fact that log b n = m iff n / (b ^ m) = 1.

    log b Zero              = Zero     -- round down
    log b (Succ Zero)       = Zero
    log b n@(Succ (Succ m)) = Succ (log b (divN n b))

This means that we will be unfolding on n.  Using the universal
property of unfoldN, we have:

    logN b = unfoldN p f

    iff

    logN b n = if p n then Zero else Succ (logN b (f n))

Using the recursive equations above, we define:

    p Zero            = True
    p (Succ Zero)     = True
    p (Succ (Succ n)) = False

When p is false, we reason:

      logN b n = Succ (logN b (f n))

    ≡   { n > 1, log.3 }

      Succ (logN b (divN n b)) = Succ (logN b (f n))

    ≡   { abstraction }

      Succ (logN b ((λm -> divN m b) n)) = Succ (logN b (f n))

which gives us a solution for f.

    logN b = unfoldN p f
      where
        p Zero            = True
        p (Succ Zero)     = True
        p (Succ (Succ n)) = False
        f m = divN m b
