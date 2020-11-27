# Exercise 3.39

We know that bff is a hylomorphism:

    bff = concatL ∘ levelf
        = foldL appendL Nil ∘ unfoldL nil (mapL root) (concatL ∘ mapL kids)

Define bff as an instance of hyloL, then deforest the intermediate list.

hyloL def., for reference:

    hyloL f e p g h = foldL f e ∘ unfoldL p g h

The definition is then easy:

    bff = hyloL appendL Nil nil (mapL root) (concatL ∘ mapL kids)

Now we need to deforest:

    bff ts =
      if nil ts
        then Nil
        else appendL (mapL root ts)
          hyloL appendL Nil nil (mapL root) (concatL ∘ mapL kids)
            (concatL (mapL kids ts))

We have a solution for the case ts = Nil, so we consider the case
ts ≠ Nil.

      bff ts

    =  { bff.1 above, nil.1, ITE }

      appendL (mapL root ts)
        (hyloL appendL Nil nil (mapL root) (concatL ∘ mapL kids)
          (concatL (mapL kids ts)))

    =  { spec. }

      appendL (mapL root ts) (bff (concatL (mapL kids ts)))

Can we improve this?
