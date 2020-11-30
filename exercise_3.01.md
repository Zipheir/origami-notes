# Exercise 3.1 (fusion law)

NTS: For strict h,

    h ∘ foldL f e = foldL f′ e′

holds if

    (h (f a b) = f′ a (h b)) ∧ (h e = e′)

Proof: Using the universal property of foldL, it holds that
h ∘ foldL f e = foldL f′ e′ if we can show the following:

   (h ∘ foldL f e) Nil         = e′
   (h ∘ foldL f e) (Cons y ys) = f′ y ((h ∘ foldL f e) ys)

So we have two cases to deal with.

We assume that

    h (f a b) = f′ a (h b)   (A)
    h e = e′                 (B)

Case Nil:

      (h ∘ foldL f e) Nil
    ≡
      h (foldL f e Nil)
    =  { foldL.1 }
      h e
    =  { B }
      e′

which establishes the case.

Case (Cons y ys):

      h (foldL f e (Cons y ys))
    =  { foldL.2 }
      h (f y (foldL f e ys))
    =  { A }
      f′ y (h (foldL f e ys))
    ≡
      f′ y ((h ∘ foldL f e) ys)

which establishes the case. ∎

Why doesn’t the law hold for non-strict h?
