## Exercise 3.27

How do ‘until p f’ and ‘untilN p f’ differ for non-strict f?

The definition of until (p. 51):

    until ∷ (a -> Bool) -> (a -> a) -> a -> a
    until p f x = if p x then x else until p f (f x)

Since the definition of ‘untilN’ that we calculated in the last
exercise is identical to this one, the exercise must refer to the
original definition (in terms of foldN and unfoldN):

    untilN ∷ (a -> Bool) -> (a -> a) -> a -> a
    untilN p f x = foldN x f (unfoldN p f x)
