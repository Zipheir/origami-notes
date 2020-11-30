# Exercise 3.5

List paramorphism operator:

      paraL ∷ (α → (List α, β) → β) → β → List α → β
      paraL f e Nil         = e
      paraL f e (Cons x xs) = f x (xs, paraL f e xs)

insert as a paraL instance:

      insertPara y = paraL f (wrap y)
        where
          f x (xs, ys) = if y < x
                           then Cons y (Cons x xs)
                           else Cons x ys

We will prove that insert y xs = insertPara y xs for all finite lists
xs by structural induction on xs.

Case Nil:

      insertPara y Nil
    =   { insertPara.1 }
      paraL f (wrap y) Nil
    =   { paraL.1 }
      wrap y
    =   { insert.1 }
      insert y Nil

which establishes the case.

Case Cons x xs:

      insertPara y (Cons x xs)
    =   { insertPara.1 }
      paraL f (wrap y) (Cons x xs)
    =   { paraL.2 }
      f x (xs, paraL f (wrap y) xs)
    =   { insertPara, f.1 }
      if y < x
         then Cons y (Cons x xs)
         else Cons x (paraL f (wrap y) xs)

Subcase y < x:

    =   { subcase def., if }
      Cons y (Cons x xs)
    =   { insert.2, subcase def. }
      insert y (Cons x xs)

Subcase y ≥ x:

    =   { subcase def., if }
      Cons x (paraL f (wrap y) xs)
    =   { hypothesis }
      Cons x (insert y xs)
    =   { insert.2, subcase def. }
      insert y (Cons x xs)

which establishes the case. ∎
