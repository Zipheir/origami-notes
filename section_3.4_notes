# Flattening trees

This section is my own interpolation.  The depth-first section uses the
dft and dff functions, but doesn’t show how to derive them as folds.

We can define a depth-first flattening function by

    dft ∷ Rose α → List α
    dft (Node a ts) = Cons a (concatL (mapL dft ts))

where concatL is the familiar list fold:

    concatL ∷ List (List α) → List α
    concatL = foldL append Nil

We can calculate a foldR instance for dft, and an accompanying function
for Forests.

Using the universal property of foldR, we have

    dft (Node a ts) = f a (foldF f g ts)

and reason as follows:

      f a (foldF f g ts) = dft (Node a ts)

    ≡   { dft.1 }

      f a (foldF f g ts) = Cons a (concatL (mapL dft ts))

If we can derive a solution for

    concatL ∘ mapL dft = foldF f g     (*)

with the induction hypothesis dft = foldR f g, we can take f = Cons.
So for (finite) ts ∷ Forest α:

      foldF f g ts = concatL (mapL dft ts)

    ≡   { foldF.1 }

      g (mapL (foldR f g) ts) = concatL (mapL dft ts)

    ≡   { hypothesis }

      g (mapL dft ts) = concatL (mapL dft ts)

    ≡   { generalizing (mapL dft ts), rewrite point-free }

      g = concatL

So we can take f = Cons, which gives us the desired definition:

    dft = foldR Cons concatL

Using this def. in (*) above, we have

    foldF f g ts = concatL (mapL (foldR Cons concatL) ts)

and so

    dff = foldF Cons concatL


### sumR

How about a function defined by

    sumR ∷ Num α ⇒ Rose α → α
    sumR = sum ∘ dft

where

    sum ∷ Num α ⇒ List α → α
    sum = foldL + 0

We seek a solution for f and g in the following:

    sumR = foldR f g

Thinking in terms of foldR fusion, we have

    sum (foldR Cons concatL) = foldR f g

    holds if

    (g ∘ mapL sum = sum ∘ concatL)
      ∧
    (∀x (f x) ∘ sum = sum ∘ (Cons x))

The first equation is actually the canonical example of the ‘bookeeping
law’ (Bird, IFPH p. 132):

    sum ∘ concatL = sum ∘ mapL sum

So we have g = sum.

We need to derive something for f.

    (f x) ∘ sum = sum ∘ (Cons x)

It’s pretty clear what we’re going to get.  But let’s calculate.

    sum (Cons x xs) = foldL + 0 (Cons x xs)
                    = x + (foldL + 0 xs)
                    = (+ x) (sum xs)

so we have f = (+).  We can now apply foldR fusion:

    sumR = foldR + sum


## Unfolds for trees and forests

We have the following mutually recursive unfolds for rose trees:

    unfoldR ∷ (β → α) → (β → List β) → β → Rose α
    unfoldR f g x = Node (f x) (unfoldF f g x)

    unfoldF ∷ (β → α) → (β → List β) → β → Forest α
    unfoldF f g x = mapL (unfoldR f g) (g x)

It's interesting to note that g is likely an unfoldL instance.

Eliminators for convenience:

    root ∷ Rose α → α
    root (Node x _) = x

    kids ∷ Rose α → Forest α
    kids (Node _ ts) = ts


## Breadth-first traversal

BFT “goes against the grain” because it is not compositional: we can’t
define traversing a forest in terms of traversing its trees.

## Level-order traversal

“The level-order traversal of a list is obtained by gluing together the
traversals of its trees.”

    levelt ∷ Rose α → List (List α)
    levelf ∷ Forest α → List (List α)

    (levelt, levelf) = (foldR f g, foldF f g)
      where
        f x xss = Cons (wrap x) xss
        g       = foldL (lzw appendL) Nil

This gives us a list of level-lists.  e.g.

       A
     / | \
    B  C  D      ⇒  [[A], [B, C, D], [E, F, G], [H]]
    |     | \
    E     F  G
          |
          H

lzw (“long zip with”) is just a variant of zipWith:

    lzw ∷ (α → α → α) → List α → List α → List α
    lzw f Nil ys                  = ys
    lzw f xs Nil                  = xs
    lzw f (Cons x xs) (Cons y ys) = Cons (f x y) (lzw f xs ys)

It is straightforward to define a breadth-first traversal in terms
of level-order traversal:

    bft ∷ Rose α → List α
    bft = concatL ∘ levelt

    bff ∷ Forest α → List α
    bff = concatL ∘ levelf


We can eliminate the repeated list concatenations of levelt and
levelf by using accumulating parameters.  The specifications are:

    levelt' ∷ Rose α → List (List α) → List (List α)
    levelt' t = lzw appendL (levelt t)

    levelf' ∷ Forest α → List (List α) → List (List α)
    levelf' ts = lzw appendL (levelf ts)


## Level-order traversal as an unfold

We can also express levelt and levelf as list unfolds.

    levelf = unfoldL nil (mapL root) (concatL ∘ mapL kids)
