# Exercise 3.7

Prove the fusion law:

    (unfoldL p f g) ∘ h = unfoldL p′ f′ g′

    if (⇐)

    (p ∘ h = p′) ∧ (f ∘ h = f′) ∧ (g ∘ h = h ∘ g′)

Proof: Define, as above,

    p′    = p ∘ h
    f′    = f ∘ h
    g ∘ h = h ∘ g′

Applying the universal property, we have

    (unfoldL p f g ∘ h) = unfoldL p′ f′ g′

    ⇔

    (unfoldL p f g ∘ h) b =
      if p′ b
        then Nil
        else Cons (f′ b) ((unfoldL p f g ∘ h) (g′ b))

We reason:

      (unfoldL p f g ∘ h) b

    ≡   { apply h, unfoldL.1 }

      if p (h b) then Nil else Cons (f (h b)) (unfoldL p f g (g (h b)))

    ≡   { unapply all occurrences of h and rewrite as compositions }

      if (p ∘ h) b then Nil else Cons ((f ∘ h) b) (unfoldL p f g ((g ∘ h) b))

    ≡   { p′ = p ∘ h, f′ = f ∘ h, g ∘ h = h ∘ g′ }

      if p′ b then Nil else Cons (f′ b) (unfoldL p f g ((h ∘ g′) b))

    ≡   { apply g′, rewrite as composition }

      if p′ b then Nil else Cons (f′ b) ((unfoldL p f g ∘ h) (g′ b))

which allows us to apply the fusion law.  We thus have

    unfoldL p f g ∘ h = unfoldL p′ f′ g′

as required. ∎
