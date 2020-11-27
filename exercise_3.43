# Exercise 3.43

(a) Define a function to perform a single h-sort on a list:

    hsort ∷ Ord α ⇒ Nat -> List α -> List α

Easy:

    hsort n = ravel ∘ mapL isort ∘ unravel n


(b) The final function is also easy.

    shell ∷ Ord α ⇒ List Nat → List α → List α
    shell Nil xs         = xs
    shell (Cons n ns) xs = shell ns (hsort n xs)

The fold version is just as easy, although probably a bit less
efficient:

    shellF ns xs = (foldL (λn f → hsort n ∘ f) ns) xs
