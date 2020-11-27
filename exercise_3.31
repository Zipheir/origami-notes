## Exercise 3.31

The (dft, dff) functions give an inefficient implementation of
depth-first traversal (why?); a more efficient version can be calculated
using fusion.

These functions are inefficient since we end up applying concatL to
ever subtree, giving us (depth e) concats for each leaf-node e when
applying dft to a tree:

    dft (Node a [Node b [Node c []],
                 Node d [Node e [Node f []]]])

    ==>

    a : (concatL [b : (concatL [[c]]),
                  d : (concatL [e : concatL [[f]]])])

(Using Haskell list syntax.)

This is actually a general problem for functions of the form ‘foldR f g’
where g is a list fold.

I’m not sure what fusion theorems Gibbons has in mind here.  foldL-mapL
fusion could be used, but it does little and trashes the definition of
dff as a foldF.

Bird in IFPH calculates a solution using an accumulating parameter.

TODO
