## Exercise 3.14

We’d like ‘insert’ to be able to make use of the remainder of the
input list; using unfold, this isn't possible, so the entire input
list must be traversed regardless of where the insertion occurs.

To fix this, we can define ‘insert’ as an *apomorphism* using the
following higher-order function:

    apoL′ ∷ (β → Maybe (α, Either β (List α))) → β → List α
    apoL′ f u = case f u of
                  Nothing            → Nil
                  Just (x, Left v)   → Cons x (apoL′ f v)
                  Just (x, Right xs) → Cons x xs

(BTW, it’s straightforward to define unfoldL′ as an apomorphism:

    unfoldL′ f = apoL′ (g ∘ f)
      where
        g Nothing     = Nothing
        g Just (x, v) = Just (x, Left v)

Using the Maybe monad, we have g = fmap (mapSnd Left).

So, we have

    insert″ y = apoL' f u

for some

    f ∷ (β → Maybe (α, Either β (List α)))
    u ∷ β

What is β here?  For a first try, we just plug-in the ‘state’ type of
insert': (List α, Maybe α).

(Is there a method by which we could calculate a definition?  Like
unfoldL and unfoldL', apoL' is tough to calculate with.)

    insert″ y xs = apoL' ins' (xs, Just y)

    ins' ∷ (List α, Maybe α) → Maybe (α, Either (List α, Maybe α) (List α))
    ins' (Nil, Nothing)       = Nothing
    ins' (Nil, Just y)        = Just (y, Right Nil)
    ins' (Cons x xs, Nothing) = Just (x, Right xs)
    ins' (Cons x xs, Just y)
      | y < x                 = Just (y, Right (Cons x xs))
      | otherwise             = Just (x, Left (xs, Just y))

ins' is pretty awkward.  There are a bunch of almost-overlapping cases
and a general sense of redundancy.  Fortunately, we can simplify this
definition.  The key realization is that the to-be-inserted value (or
its absence) no longer need to be part of the ‘state’; we can thus
parameterize ins' over this value.

    ins' ∷ α -> List α → Maybe (α, Either (List α, Maybe α) (List α))

    ins' y Nil         = Just (y, Right Nil)
    ins' y (Cons x xs)
      | y < x          = Just (y, Right (Cons x xs))
      | otherwise      = Just (x, Left xs)

    insert″ y = apoL' (ins' y)

This is much nicer.


NTS: insert″ y xs = insert y xs, for finite lists xs.

The proof is by structural induction on xs.

Case Nil:

      insert″ y Nil

    =   { insert″.1 }

      apoL' (ins' y) Nil

    =   { apoL'.1 }

      case ins' y Nil of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

    =   { ins'.1 }

      case Just (y, Right Nil) of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

    =   { case, pattern matching }

      Cons y Nil

    =   { wrap.1, insert.1 }

      insert y Nil

which establishes the case.

Case (Cons z zs):

      insert″ y (Cons z zs)

    =   { insert″.1 }

      apoL' (ins' y) (Cons z zs)

    =   { apoL'.1 }

      case ins' y (Cons z zs) of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

We have two subcases to consider.

Subcase y < z:

    =   { ins'.2 }

      case Just (y, Right (Cons z zs)) of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

    =   { case, pattern matching }

      Cons y (Cons z zs)

    =   { insert.2, y < z }

      insert y (Cons z zs)

Subcase y ≥ z:

      case ins' y (Cons z zs) of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

    =   { ins'.2 }

      case Just (z, Left zs) of
        Nothing            → Nil
        Just (x, Left v)   → Cons x (apoL′ f v)
        Just (x, Right xs) → Cons x xs

    =   { case, pattern matching }

      Cons z (apoL' (ins' y) zs)

    =   { hypothesis }

      Cons z (insert y zs)

    =   { insert.2, subcase def. }

      insert y (Cons z zs)

which establishes the case. ∎
