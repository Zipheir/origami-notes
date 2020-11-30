## Exercise 3.20

(a) Define

    subN ∷ Nat → Nat → Maybe Nat

as a foldN instance.

Our recursive definition of the function is

    subN Zero Zero         = Just Zero
    subN (Succ m) Zero     = Just (Succ m)
    subN Zero (Succ n)     = Nothing
    subN (Succ m) (Succ n) = subN m n

We′ve written disjoint cases, but the first two could be unified if we
assume sequential testing.

We have

    subN m = foldN (Just m) pred
      where
        pred Nothing  = Nothing
        pred (Just n) = predN n

TODO: derive this or prove that it holds.

(b) Define eqN ∷ Nat → Nat → Bool

    eqN m n = case subN m n of
                Just Zero     -> True
                Just (Succ x) -> False

(c) Define lessN ∷ Nat → Nat → Bool

    lessN m n = case subN m n of
                  Nothing -> True
                  Just _  -> False
