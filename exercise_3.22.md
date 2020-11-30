## Exercise 3.22

What is the universal property of ‘unfoldN’?

Presumably, it’s

    h = unfoldN p f

    iff

    h x = if p x
            then Zero
            else Succ (h (f x))

for all h ∷ α → Nat.

For the fusion law, we expect it to be similar to that for list unfold:

    (unfoldN p f) ∘ g = unfoldN p' f'

With the universal property, we have

    (unfoldN p f) ∘ g = unfoldN p' f'

    iff

    ((unfoldN p f) ∘ g) x = if p' x
                              then Zero
                              else Succ (((unfoldN p f) ∘ g) (f x))

Given  p' x = True, we (try to) reason:

      ((unfoldN p f) ∘ g) x = Zero

    ≡   { application, unfoldN.1 }

      if p (g x) then Zero else ... = Zero

Defining p (g x) ⇒ p' x gives us a solution here.

In the case p' x = False, we have:

      ((unfoldN p f) ∘ g) x = Succ (((unfoldN p f) ∘ g) (f' x))

    ≡   { application, unfoldN.1 }

      if p (g x) then Zero else Succ (unfoldn p f (f (g x)))
        = Succ (((unfoldN p f) ∘ g) (f' x))

    ≡   { application }

      if p (g x) then Zero else Succ (unfoldN p f (f (g x)))
        = Succ (unfoldN p f (g (f' x)))

    ≡   { define: p' x = False ⇒ p (g x) = False }

      Succ (unfoldN p f (f (g x))) = Succ (unfoldN p f (g (f' x)))

    ≡   { unapplying Succ from both sides }

      unfoldN p f (f (g x)) = unfoldN p f (g (f' x))

which gives us f ∘ g = g ∘ f'.  From the constraints on p', we
also define:

    p' = p ∘ g

So

    (unfoldN p f) ∘ g = unfoldN p' f'

holds if

    (p' = p ∘ g) ∧ (f ∘ g = g ∘ f')

for all p, f, g, p', and f' of the appropriate types.  This is quite
similar to the fusion law for list unfold.
