Lex Augusteijn points out in "Sorting morphisms" that some sorting
algorithms are determined entirely by their recursion pattern.
(We can abstract the algorithm from the structure to be sorted,
if we know how to traverse that structure.)

# 3.2 Origami with lists: sorting

Some familiar definitions:

    data List α = Nil | Cons α (List α)

    wrap ∷ α → List α
    wrap x = Cons x Nil

    nil ∷ List α → Bool
    nil Nil = True
    nil (Cons _ _) = False

This is actually the right fold; ‘L’ here is for ‘list’:

    foldL ∷ (α → β → β) → β → (List α) → β
    foldL f e Nil = e
    foldL f e (Cons x xs) = f x (foldL f e xs)

The universal property of foldL:

If h ∷ (List α) → β is some function, then

    h = foldL f e

if and only if

    h xs = case xs of
             Nil       → e
             Cons y ys → f y (h ys)

Insertion sort with explicit recursion:

    isort ∷ Ord α ⇒ List α → List α
    isort = foldL insert Nil
      where
        insert ∷ Ord α ⇒ α → List α → List α
        insert y Nil = wrap y
        insert y (Cons x xs)
          | y < x     = Cons y (Cons x xs)
          | otherwise = Cons x (insert y xs)


# Unfolds for lists

Unfolding is dual to folding.  The two common versions of list unfold:

    -- Maybe-based version, familiar to Data.List users.
    unfoldL′     ∷ (β → Maybe (α, β)) → β → List α
    unfoldL′ f u = case f u of
                     Nothing     → Nil
                     Just (x, v) → Cons x (unfoldL′ f v)

    -- Predicate-based version.
    unfoldL         ∷ (β → Bool) → (β → α) → (β → β) → β → List α
    unfoldL p f g b = if p b
                        then Nil
                        else Cons (f b) (unfoldL p f g (g b))

(Note: wrap as an unfold is pretty trivial, but we can’t write it
directly because we’d need a value of the same type as x that is not x
to stop the unfold.  We have to do an interesting little dance:

    wrap x = unfoldL isNothing fromJust (const Nothing) (Just x)
)

We have a universal property for unfoldL:

    h = unfoldL p f g

    iff

    h b = if p b then Nil else Cons (f b) (h (g b))

We also have a single-argument version of foldL, analogous to
unfoldL′:

    foldL′ ∷ (Maybe (α, β) → β) → List α → β
    foldL′ f Nil         = f Nothing
    foldL′ f (Cons x xs) = f (Just (x, foldL′ f xs))


Selection sort: We unfold a sorted list from an input list by
successively taking the minimum element of the input list without
disordering the remaining sublist.

    ssort ∷ Ord α ⇒ List α → List α
    ssort = unfoldL′ delmin

    delmin ∷ Ord α ⇒ List α → Maybe (α, List α)
    delmin Nil = Nothing
    delmin xs  = Just (y, deleteL y xs)
      where y = minimumL xs

    minimumL (Cons x xs) = foldL min x xs

    deleteL ∷ Eq α ⇒ α → List α → List α
    deleteL y Nil = Nil
    deleteL y (Cons x xs)
      | y == x    = xs
      | otherwise = Cons x (deleteL y xs)

The infamous bubble sort is also an unfold.

    bsort ∷ Ord α ⇒ List α → List α
    bsort = unfoldL' bubble

    bubble ∷ Ord α ⇒ List α → Maybe (α, List α)
    bubble = foldL step Nothing
      where
        step x Nothing = Just (x, Nil)
        step x (Just (y, ys))
          | x < y      = Just (x, Cons y ys)
          | otherwise  = Just (y, Cons x ys)

‘bubble’ doesn’t maintain the relative order of the remaining list
elements, so it's possible to define it as a fold.


## Hylomorphisms

Hylomorphism = unfold followed by fold.

    hyloL f e p g h = foldL f e ∘ unfoldL p g h

For example,

    fact = hyloL (×) 1 (== 0) id pred

Hylomorphism fusion (deforestation) eliminates the intermediate
structure:

    hyloL f e p g h b = if p b
                          then e
                          else f (g b) (hyloL f e p g h (h b))

Fold-then-unfold (called a *metamorphism* by Gibbons) is more obscure,
and is a useful pattern for translation between data formats.
