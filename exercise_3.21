## Exercise 3.21

Express ‘unfoldN’ in terms of ‘unfoldN′’ and vice versa.

(a) unfoldN as an instance of unfoldN′

We need a definition of the form

    unfoldN p f x = unfoldN′ g x

First, assume p x = True:

      unfoldN p f x = unfoldN′ g x

    ≡   { unfoldN.1, p x = True }

      Zero = unfoldN′ g x

    ≡   { unfoldN′.1 }

      Zero = case g x of
               Nothing → Zero
               ...

Requiring that

    p x ⇒ g x = Nothing

gives us a solution for this case.

In the case p x = False:

      unfoldN p f x = unfoldN′ g x

    ≡   { unfoldN.1, p x = False }

      Succ (unfoldN p f (f x)) = unfoldN′ g x

    ≡   { unfoldN′.1 }

      Succ (unfoldN p f (f x)) = case g x of
                                   Nothing → Zero
                                   Just y  → Succ (unfoldN′ g y)

    ≡   { define: not (p x) ⇒ g x = Just (f x) }

      Succ (unfoldN p f (f x)) = case Just (f x) of
                                   Nothing → Zero
                                   Just y  → Succ (unfoldN′ g y)

    ≡   { case, pattern matching }

      Succ (unfoldN p f (f x)) = Succ (unfoldN′ g (f x))

I guess we could use a coinduction hypothesis to show that this
equation holds?  After this not-quite-rock-solid derivation, we have:

    unfoldN p f = unfoldN′ g
      where
        g x = if p x then Nothing else Just (f x)


(b) unfoldN′ as an instance of unfoldN

We can use the universal property of unfoldN here:

    unfoldN′ f = unfoldN p g

    iff

    unfoldN′ f x = if p x then Zero else Succ (unfoldN′ f (g x))

We need to consider two cases.

Case f x = Nothing:

      unfoldN′ f x = if p x then Zero else Succ (unfoldN′ f (g x))

    ≡   { unfoldN′.1 }

      (case f x of
         Nothing → Zero
         Just y  → Succ (unfoldN′ f y)) = if p x
                                             then Zero
                                             else Succ (unfoldN′ f (g x))

    ≡   { f x = Nothing, case, pattern matching }

      Zero = if p x then Zero else Succ (unfoldN′ f (g x))

Defining

    p x
      | f x == Nothing = True
      ...

gives us a solution to this case.

Case f x = Just y:

      unfoldN′ f x = if p x then Zero else Succ (unfoldN′ f (g x))

    ≡   { unfoldN′.1 }

      (case f x of
         Nothing → Zero
         Just z  → Succ (unfoldN′ f z)) = if p x
                                             then Zero
                                             else Succ (unfoldN′ f (g x))

    ≡   { f x = Just y }

      (case Just y of
         Nothing → Zero
         Just z  → Succ (unfoldN′ f z)) = if p x
                                             then Zero
                                             else Succ (unfoldN′ f (g x))

    ≡   { case, pattern matching }

      Succ (unfoldN′ f y) = if p x then Zero else Succ (unfoldN′ f (g x))

    ≡   { define: f x = Just y ⇒ p x = False, ITE }

      Succ (unfoldN′ f y) = Succ (unfoldN′ f (g x))

Defining g x = y gives us a solution in this case.

We have:

    unfoldN′ f = unfoldN p g
      where
        p x
          | f x == Nothing = True
          | otherwise      = False

        g x = case f x of     -- the ‘Nothing’ case can’t happen
                Just y → y

This definition is a little awkward.  As is typically the case with
defining boolean-based unfolds in terms of Maybe-based functions, we
need to derive two functions from one.  The result is apparent
redundancy.  Note that g is only invoked if (f x) is a Just value.
We could use a library function to define, equivalently,

    g = fromJust ∘ f
