# Exercise 3.41

Define list transpose as a fold, then as an unfold.

    trans ∷ List (List α) → List (List α)

It would be nice if you told us what the function *does*, Jeremy!

We can specify this function by

    trans Nil = Nil
    trans (Cons xs xss) =
      if nil xs
         then Nil
         else Cons (map head (Cons xs xss))
                (trans (map tail (Cons xs xss)))

However, this version of trans is partial; it’s undefined on lists of
unequal-length lists.  For what we’ll be using it for, it’s critical
that we write the total version.

    trans Nil            = Nil
    trans (Cons Nil xss) = trans xss
    trans xss            = Cons (map head xss') (trans (map tail xss'))
      where xss' = filter (not ∘ nil) xss

This definition is actually a bit subtle.

Let’s try the unfold version first.

(a) Anamorphism

By the universal property of unfoldL, we have

    unfoldL p f g = trans

    iff

    trans xss = if p xss
                  then Nil
                  else Cons (f xss) (trans (g xss))

Since trans xss = Nil iff xss = Nil, we have p = nil.  In the case
xss ≠ Nil, we have

    trans xss = Cons (f xss) (trans (g xss))

But we have a serious problem.  By the definition above,

    trans (Cons Nil Nil) = trans Nil = Nil,

which is not of the form Cons y ys.  So it seems we can’t proceed.

Gibbons really does not provide anywhere near enough information in
this section.  We need a total version of list transpose, but there
does not seem to be a way to define it as an unfold.  (The fold version
seems even more daunting.)
