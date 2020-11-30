# Exercise 3.9

Define the helper functions

    foldLargs ∷ (α → β → β) → β → (Maybe (α, β) → β)
    unfoldLargs ∷ (β → Bool) → (β → α) → (β → β) → (β → (Maybe (α, β)))

These allow us to define

    foldL   = foldL′ ∘ foldLargs       (*)
    unfoldL = unfoldL′ ∘ unfoldLargs   (#)

(a) foldLargs.  We can use the above plus the definition of foldL from
the previous exercise,

    foldL f e = foldL′ g
      where
        g Nothing        = e
        g (Just (x, ys)) = f x ys

to give the following equations:

    foldLargs f e Nothing        = e
    foldLargs f e (Just (x, ys)) = f x ys

This is a correct definition.  If we want to be a little clearer, we
can write

    foldLargs f e = (λm → case m of
                            Nothing      → e
                            Just (x, ys) → f x ys)

(b) unfoldLargs.

From the alternate definition of unfoldL from exercise 3.6 we have

    unfoldL p f g b = unfoldL′ h b
      where
        h u = if p u then Nothing else Just (f u, g u)

Using this and (#) above, we have the equation

    unfoldLargs p f g u = if p u then Nothing else Just (f u, g u)

Again, we can rewrite this to be a bit clearer and more consistent
with its type signature:

    unfoldLargs p f g = (λu → if p u
                                then Nothing
                                else Just (f u, g u))
