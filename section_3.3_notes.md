# 3.3 Origami by numbers

    data Nat = Zero | Succ Nat

We have a fold for natural numbers.

    foldN ∷ α → (α → α) → Nat → α
    foldN z s Zero     = z
    foldN z s (Succ n) = s (foldN z s n)

This is actually a rearranged version of the familiar ‘iterate’
function which expresses the repeated application of a given
function:

    iter ∷ Nat -> (a -> a) -> (a -> a)
    iter n f x = foldN x f n

(iter n) is the Church numeral of n.


## Unfolds for naturals

We have both a single-function and multi-function version of unfoldN,
as with unfoldL.

    unfoldN′ ∷ (a → Maybe a) → a → Nat
    unfoldN′ f x = case f x of
                     Nothing → Zero
                     Just y  → Succ (unfoldN′ f y)

    unfoldN ∷ (a → Bool) → (a → a) → a → Nat
    unfoldN p f x = if p x then Zero else Succ (unfoldN p f (f x))

“[T]his is the minimisation function from recursive function theory,
which takes a predicate p, a function f, and a value x, and computes
the least number n such that p (iter n f x) holds.” (p. 50)


## Beyond primitive recursion

The fact that we can express minimization functions as unfolds on
naturals means that we've gone past primitive recursion.   “Indeed,
using only folds and unfolds on naturals, we can capture the full
power of iterative imperative programs.” (p. 50)

We can use a hylomorphism to express the equivalent of the ‘while
loop’ of imperative programming.

    untilN ∷ (a -> Bool) -> (a -> a) -> a -> a
    untilN p f x = foldN x f (unfoldN p f x)

untilN repeatedly applies f (with initial argument x) until p is true.
The version above is simple but inefficient; it first computes the
number of applications required, then performs the iteration.  This is
a classic opportunity for deforestation.
