# Exercise 3.6

(a) Express unfoldL in terms of unfoldL′.

We seek solutions for h and u in

    unfoldL p f g b = unfoldL' h u

b and u both denote the first seed, so we say b = u.

We reason that (h u) should yield Nothing when (p b) is true:

    h u = if p b then Nothing else ...

In unfoldL, the next consed-on value is (f b) and the next seed is
(g b).  Since f returns a tuple of these values wrapped in a Maybe,
we reason:

    h u = if p b then Nothing else Just (f b, g b)

So we have

    unfoldL p f g b = unfoldL' h b
      where
        h u = if p b then Nothing else Just (f b, g b)

We prove that this definition is equivalent by case analysis.

Case (p b) = True:

      unfoldL' h b

    =  { unfoldL'.1 }

      case f u of
        Nothing     → Nil
        ...

    =  { definition of f above }

      case (if p b then Nothing else Just (f b, g b)) of
        Nothing     → Nil
        ...

    =  { (p b) = True }

      case Nothing of
        Nothing     → Nil
        ...

    =  { case }

      Nil

    =  { unfoldL.1, (p b) = True }

      unfoldL p f g b

Case (p b) = False.  We will use the (co?)induction hypothesis,

    unfoldL' h (g b) = unfoldL p f g (g b)

though I'm not sure whether this is the right form for such a thing.

FIXME: We can just define unfoldL' h = unfoldL p f g, I think.

      unfoldL' h b

    =  { unfoldL'.1 }

      case f u of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL′ f v)

    =  { def. of f above }

      case (if p b then Nothing else Just (f b, g b)) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL′ f v)

    =  { p b = False, if }

      case Just (f b, g b) of
        Nothing → Nil
        Just (x, v) → Cons x (unfoldL′ f v)

    =  { case, pattern-matching }

        Cons (f b) (unfoldL' f (g b))

    =  { hypothesis }

        Cons (f b) (unfoldL p f g (g b))

    =  { unfoldL.1, p b = False }

        unfoldL p f g b

which establishes the case. ∎


(b) Express unfoldL′ in terms of unfoldL.

Jumping ahead slightly, we use the universal property of unfoldL:

    unfoldL' f' = unfoldL p f g

    iff

    unfoldL' f' b = if p b then Nil else Cons (f b) (unfoldL' f' (g b))
