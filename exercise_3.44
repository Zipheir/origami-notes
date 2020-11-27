# Exercise 3.44

“Can the ‘ravel’ of one ‘hsort’ and the ‘unravel’ of the next be fused
as a hylomorphism?“

What does this mean, exactly?  ‘Fusion’ means something a bit
different for hylomorphisms, in this book (namely, deforestation).
‘ravel’ and ‘unravel’ can both be seen as hylomorphisms (by using the
anamorphism and catamorphism definitions of ‘trans’, respectively),
but we don’t have a fusion law in the style of fold/unfold fusion for
hyloL by which the two hylomorphisms could be combined.  So presumably
Gibbons means for us to solve the equation

    hyloL f e p g h b = unravel n ∘ ravel

which means we need to solve

    unfoldL p g h = ravel

    foldL f e     = unravel n

Trying to come up with an unfold version of ravel seems pretty
tough:

    ravel = concatL ∘ trans

The presence of concatL means we’re appending successive values,
making it difficult to solve for g and h.
