# 3.5 Other sorts of origami

## Shell sort

Shell sort h-sorts a list for values of h.  A list is h-sorted if,
for each value of i, the subsequence of elements at positions i, i+h,
i + 2h, ... is sorted.  h-sorting for large values of h makes it easier
for small values.

In functional terms, one way to describe h-sorting is as unravelling the
list into h sublists, sorting each, then ravelling them back together.

Given a list transpose function ‘trans’ (which is either a fold or an
unfold; c.f. exercise 3.41), we can define ravelling by

    ravel ∷ List (List α) → List (List α)
    ravel = concatL ∘ trans

unravel ∷ Nat → List α → List (List α) is defined in terms of ‘takeL’
and ‘dropL’ and splits a list into n-length consecutive sublists, with
the last sublist being shorter if necessary.
