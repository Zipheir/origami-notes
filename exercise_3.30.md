## Exercise 3.30

We can get something that looks like a universal property for each
of foldR and foldF by subbing-in the definition of the other function.
For h ∷ Rose α → β, we have

    h = foldR f g

    iff

    h (Node a ts) = f a (foldF f g ts)

And for h ∷ Forest α → γ:

    h = foldF f g

    iff

    h ts = g (mapL (foldR f g) ts)

Unfortunately, expanding this last equation using the equations for
mapL (by case analysis on ts) doesn’t clarify things much.  So here
it stands.

### Fusion

Here are the equations we are interested in solving:

    h ∘ foldR f g = foldR f′ g′, for all h ∷ β → δ

    h ∘ foldF f g = foldF f′ g′, for all h ∷ γ → δ

We can use the universal property of foldR.

    h ∘ foldR f g = foldR f′ g′

    iff

    (h (foldR f g (Node x ts))) = f′ x (foldF f′ g′ ts)

Let’s look at the foldF fusion law first.  Using the universal property,
we have

    h ∘ foldF f g = foldF f′ g′

    iff

    h (foldF f g ts) = g′ (mapL (foldR f′ g′) ts)

We can derive a constraint for the g′ function:

      h (foldF f g ts) = g′ (mapL (foldR f′ g′) ts)

    ≡   { foldF.1 }

      h (g (mapL (foldR f g) ts)) = g′ (mapL (foldR f′ g′) ts)

    ≡   { universal property of foldR }

      h (g (mapL (foldR f g) ts)) = g′ (mapL (h ∘ foldR f g) ts)

    ≡   { mapL fusion }

      h (g (mapL (foldR f g) ts)) = g′ (mapL h (mapL (foldR f g) ts))

    ≡   { generalizing (mapL (foldR f g) ts) to ys }

      h (g ys) = g′ (mapL h ys)

    ≡   { rewrite as composition }

      h ∘ g = g′ ∘ mapL h

Can we use this equation to derive a constraint for f′?  Let’s assume
that it holds for h, g, and g′ in the following.  We return to the
equation that we got from applying the universal property, and reason
as follows:

      f′ x (foldF f′ g′ ts) = h (foldR f g (Node x ts))

    ≡   { foldR.1 }

      f′ x (foldF f′ g′ ts) = h (f x (foldF f g ts))

    ≡   { foldF.1, twice }

      f′ x (g′ (mapL (foldR f′ g′) ts)) = h (f x (g (mapL (foldR f g) ts)))

    ≡   { universal property of foldR }

      f′ x (g′ (mapL (h ∘ foldR f g) ts)) = h (f x (g (mapL (foldR f g) ts)))

    ≡   { mapL fusion }

      f′ x (g′ (mapL h (mapL (foldR f g) ts))) = h (f x (g (mapL (foldR f g) ts)))

    ≡   { g′ ∘ mapL h = h ∘ g }

      f′ x (h (g (mapL (foldR f g) ts))) = h (f x (g (mapL (foldR f g) ts)))

    ≡   { generalizing (mapL (foldR f g) ts) to ys }

      f′ x (h (g ys)) = h (f x (g ys))

    ≡   { rewrite as point-free composition }

      (f′ x) ∘ h ∘ g = h ∘ (f x) ∘ g

    ≡   { generalizing to eliminate g }

      (f′ x) ∘ h = h ∘ (f x)

which gives us another constraint.

So far, we′ve established that

    h ∘ foldF f g = foldF f′ g′ ⇐ g′ ∘ mapL h = h ∘ g

    h ∘ foldR f g = foldR f′ g′ ⇐
        (g′ ∘ mapL h = h ∘ g) ∧ (∀x (f′ x) ∘ h = h ∘ (f x))

Does the second requirement for foldR also hold for f, g, h, and f′ in
foldF?  Given both constraints, can we derive

    h ∘ foldF f g = foldF f′ g′

It seems that we should be able to, since they give us an “induction
hypothesis” in the form of the fusion law for foldR.

So let’s assume

    g′ ∘ mapL h = h ∘ g            (I)
    ∀x (f′ x) ∘ h = h ∘ (f x)      (II)

We reason as follows: For finite Forests ts,

      h (foldF f g ts)

    ≡   { foldF.1 }

      h (g (mapL (foldR f g) ts))

    ≡   { unapply h and g, (I), apply g′ ∘ mapL h }

      g′ (mapL h (mapL (foldR f g) ts))

    ≡   { mapL fusion }

      g′ (mapL (h ∘ foldR f g) ts)

    ≡   { (I) + (II) + foldR fusion }

      g′ (mapL (foldR f′ g′) ts)

    ≡   { foldF.1 }

      foldF f′ g′ ts

as required. ∎  So (II) is actually only required to apply foldR fusion,
and is otherwise unused.
