## Exercise 3.26

We have a deforestation-friendly version of untilN,

    untilN2 :: (a -> Bool) -> (a -> a) -> a -> a -> a
    untilN2 p f x y = foldN x f (unfoldN p f y)

satisfying

    untilN p f x = untilN2 p f x x

NTS:

    (1)  untilN2 p f x y = if p y then x else untilN2 p f (f x) (f y)

    (2)  untilN p f x = if p x then x else untilN p f (f x)

### 1

We're trying to deforest untilN2.

We calculate using a case analysis on the predicate p.

      untilN2 p f x y = foldN x f (unfoldN p f y)

    ≡   { unfoldN.1 }

      untilN2 p f x y = foldN x f (if p y
                                     then Zero
                                     else Succ (unfoldN p f (f y)))

Case p y = True:

    ≡   { ITE }

      untilN2 p f x y = foldN x f Zero

    ≡   { foldN.1 }

      untilN2 p f x y = x

which gives us a solution for the case.

Case p y = False:

      untilN2 p f x y = foldN x f (if p y
                                     then Zero
                                     else Succ (unfoldN p f (f y)))

    ≡   { ITE }

      untilN2 p f x y = foldN x f (Succ (unfoldN p f (f y)))

    ≡   { foldN.2 }

      untilN2 p f x y = f (foldN x f (unfoldN p f (f y)))

    ≡   { rewrite as composition }

      untilN2 p f x y = (f ∘ foldN x f) (unfoldN p f (f y))

    ≡   { foldN fusion }

      untilN2 p f x y = foldN (f x) f (unfoldN p f (f y))

    ≡   { specification }

      untilN2 p f x y = untilN2 p f (f x) (f y)

which gives the second solution.  Combining the two cases, we have

      untilN2 p f x y = if p y then x else untilN2 p f (f x) (f y)

which is the required deforested definition of untilN2.

### 2

We begin with our definition of untilN in terms of untilN2, and reason
as follows.

      untilN p f x = untilN2 p f x x

    ≡   { untilN2.1 }

      untilN p f x = if p x then x else untilN2 p f (f x) (f x)

    ≡   { specification }

      untilN p f x = if p x then x else untilN p f (f x)

as required. ∎
