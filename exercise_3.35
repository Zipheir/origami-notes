We can eliminate the repeated list concatenations of levelt and
levelf by using accumulating parameters.  The specifications are:

    levelt' ∷ Rose α → List (List α) → List (List α)
    levelt' t = lzw appendL (levelt t)

    levelf' ∷ Forest α → List (List α) → List (List α)
    levelf' ts = lzw appendL (levelf ts)


## Exercise 3.35

Derive the definitions of ‘levelt'’ and ‘levelf'’.

The point-free versions of the specs. above come in handy:

    levelt' = lzw appendL ∘ levelt
    levelf' = lzw appendL ∘ levelf

For convenience:

    (levelt, levelf) = (foldR f g, foldF f g)
      where
        f x xss = Cons (wrap x) xss
        g       = foldL (lzw appendL) Nil

(a) levelt'

We have the specification

    levelt' t xss = lzw appendL (levelt t) xss

We consider the tree t and the accumulating parameter xss.

Case t = (Node a Nil), xss = Nil:

      lzw appendL (levelt (Node a Nil)) Nil

    =   { lzw.2 }

      levelt (Node a Nil)

    =   { levelt.1, foldR.1 }

      f a (foldF f g Nil)
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { foldF.1, mapL.1 }

      f a (g Nil)
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { g def., foldL.1 }

      f a Nil
        where
          f x xss = Cons (wrap x) xss

    =   { f def. }

      Cons (wrap a) Nil

which gives us a solution for this case.

We can extract a part of the above as a useful shortcut-lemma:

Lemma 1:

    levelt (Node a Nil) = Cons (wrap a) Nil

Proof: See above.

Case (Cons xs xss):

      lzw appendL (levelt (Node a Nil)) (Cons xs xss)

    =   { lemma 1 }

      lzw appendL (Cons (wrap a) Nil) (Cons xs xss)

    =   { lzw.4 }

      Cons (appendL (wrap a) xs) (lzw appendL xss Nil)

    =   { lzw.2 }

      Cons (appendL (wrap a) xs) xss

    =   { wrap.1, appendL.1 & 2 }

      Cons (Cons a xs) xss

which gives a solution for the case.

Case (Node a ts), ts ≠ Nil, xss = Nil:

      lzw appendL (levelt (Node a ts)) Nil

    =   { levelt.1 }

      lzw appendL (foldR f g (Node a ts)) Nil
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { foldR.1, f def. }

      lzw appendL (Cons (wrap a) (foldF f g ts)) Nil
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { lzw.2 }

      Cons (wrap a) (foldF f g ts)
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { lzw.2, levelf.1 }

      Cons (wrap a) (lzw appendL (levelf ts) Nil)

    =   { rewrite as composition, specification }

      Cons (wrap a) (levelf' ts Nil)

which gives us a solution for this case.

We can unify this with the first equation by observing that

    levelf' Nil Nil = Nil,

and so Cons (wrap a) Nil = Cons (wrap a) (levelf' Nil Nil).

Quick proof:

    levelf' ts Nil
      = lzw appendL (levelf Nil) Nil
      = lzw appendL (foldF f g Nil) Nil
          where g = foldL (lzw appendL) Nil
      = lzw appendL (g (mapL (foldR f g) Nil)) Nil
      = lzw appendL (g Nil) Nil
      = lzw appendL Nil Nil
      = Nil

So we have, thus far,

    levelt' (Node a ts) Nil            = Cons (wrap a) (levelf' ts Nil)
    levelt' (Node a Nil) (Cons xs xss) = Cons (Cons a xs) xss

Case (Node a ts), ts ≠ Nil, (Cons xs xss):

      lzw appendL (levelt (Node a ts)) (Cons xs xss)

    =   { levelt.1 }

      lzw appendL (foldR f g (Node a ts)) (Cons xs xss)
        where
          f y yss = Cons (wrap y) yss
          g       = foldL (lzw appendL) Nil

    =   { foldR.1, f def. }

      lzw appendL (Cons (wrap a) (foldF f g ts)) (Cons xs xss)
        where
          f y yss = Cons (wrap y) yss
          g       = foldL (lzw appendL) Nil

    =   { lzw.4 }

      Cons (appendL (wrap a) xs) (lzw appendL (foldF f g ts) xss)
        where
          f y yss = Cons (wrap y) yss
          g       = foldL (lzw appendL) Nil

    =   { rewrite as composition, specification }

      Cons (appendL (wrap a) xs) (levelf' ts xss)

    =   { wrap.1, appendL.1 & 2 }

      Cons (Cons a xs) (levelf' ts xss)

We can replace the previously-derived equation

    levelt' (Node a Nil) (Cons xs xss) = Cons (Cons a xs) xss

with what we’ve derived above by generalizing Nil to ts, provided we
can show that

    levelf' Nil xss = xss

for finite lists xss.

Quick proof:

    levelf' Nil xss
      = lzw appendL (levelf Nil) xss

      = lzw appendL (foldF f g Nil) xss
          where
            f x xss = Cons (wrap x) xss
            g       = foldL (lzw appendL) Nil

      = lzw appendL (g (mapL (foldR f g) Nil)) xss

      = lzw appendL (foldL (lzw appendL) Nil Nil) xss

      = lzw appendL Nil xss

      = xss
∎

So we have

    levelt' (Node a ts) Nil            = Cons (wrap a) (levelf' ts Nil)
    levelt' (Node a ts) (Cons xs xss)  = Cons (Cons a xs) (levelf' ts xss)

This semi-completes the synthesis of levelt'; to complete it, we must
still calculate a definition for levelf'.


(b) levelf'

We have the specification

    levelf' ∷ Forest α → List (List α) → List (List α)
    levelf' = lzw appendL ∘ levelf

We calculate by case analysis on the input Forest and accum-list.

Case Nil, xss: Immediate from the above quicky proof:

    levelf' Nil xss = xss

Case (Cons t ts), xss:

      lzw appendL (levelf (Cons t ts)) xss

    =   { levelf.1 }

      lzw appendL (foldF f g (Cons t ts)) xss
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { foldF.1 }

      lzw appendL (g (mapL (foldR f g) (Cons t ts))) xss
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { g def. }

      lzw appendL (foldL (lzw appendL) Nil (mapL (foldR f g) (Cons t ts))) xss
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { foldL-mapL fusion }

      lzw appendL (foldL (lzw appendL ∘ foldR f g) Nil (Cons t ts)) xss
        where
          f x xss = Cons (wrap x) xss
          g       = foldL (lzw appendL) Nil

    =   { levelt.1 }

      lzw appendL (foldL (lzw appendL ∘ levelt) Nil (Cons t ts)) xss

    =   { specification }

      lzw appendL (foldL levelt' Nil (Cons t ts)) xss

How can we proceed?  We have the types

    xss                                             ∷ List (List α)
    foldL levelt' Nil (Cons t ts)                   ∷ List (List α)
    lzw appendL (foldL levelt' Nil (Cons t ts)) xss ∷ List α

We should be able to eliminate the lzw appendL, as we did in the
definition of levelf'.  Let’s try to move forward by a case analysis
on xss.

Case xss = Nil:

      lzw appendL (foldL levelt' Nil (Cons t ts)) Nil

    =   { foldL.2 }

      lzw appendL (levelt' t (foldL levelt' Nil ts)) Nil

Since we know that (levelt' t xs) is non-empty for all finite xs, we
can just applying lzw.2 and jump to:

    foldL levelt' Nil (Cons t ts)

So far, we have

    levelf' Nil xss         = xss
    levelf' (Cons t ts) Nil = foldL levelt' Nil (Cons t ts)

Using foldL.1 (foldL f xss Nil = xss), we can generalize the second
equation to encompass the first.

    levelf' ts xss = foldL levelt' xss ts

Actually, this gives us a complete definition!  We don’t need to get
any further into the weeds with the case xss ≠ Nil.

While we eventually solved this exercise, the derivations were pretty
hairy and involved a lot of blundering around to derive redundant
results.  Can we calculate these functions more elegantly?
