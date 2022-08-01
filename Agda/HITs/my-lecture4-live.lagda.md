```agda
-- rewriting makes equalities behave like def. equality
{-# OPTIONS --without-K --rewriting #-}

open import new-prelude

module my-lecture4-live where

-- Inductive types have pount constructors, higher inductive types have path constructors, and paths between paths.

-- Use postulate to postulate higher inductive types because default Agda has no suport for this

-- First example:  The circle

postulate
  S1 : Type
  base : S1
  loop : base ≡ base [ S1 ] -- [ _ ] notation to specify type of
                            -- identity explicitly

example-path : base ≡ base
example-path = loop ∙ (! loop ∙ loop) -- f ∙ g means go along f then go along g, ! f is the inverse

-- show that example path is just loop

example : example-path ≡ loop [ base ≡ base [ S1 ] ]
example = {!!} -- not yet

-- path induction gives yoou the groupoid laws, e.g.

∙assoc : {A : Type} {x y z w : A}
         (p : x ≡ y)
         (q : y ≡ z)
         (r : z ≡ w)
         → p ∙ (q ∙ r) ≡ (p ∙ q) ∙ r
∙assoc (refl _) (refl _) (refl _) = refl (refl _)

∙unit-l : {A : Type} {x y : A}
        → (p : x ≡ y)
        → (refl _ ∙ p) ≡ p
∙unit-l (refl _) = refl _

∙unit-r : {A : Type} {x y : A}
        → (p : x ≡ y)
        → (p ∙ refl _) ≡ p
∙unit-r p = refl p

!-inv-l : {A : Type} {x y : A}
        → (p : x ≡ y)
        → (! p ∙ p) ≡ refl y
!-inv-l (refl _) = refl _

!-inv-r : {A : Type} {x y : A}
        → (p : x ≡ y)
        → (p ∙ ! p) ≡ refl x
!-inv-r (refl _) = refl _

example' : example-path ≡ loop [ base ≡ base [ S1 ] ]
example' = loop ∙ (! loop ∙ loop)
         ≡⟨ ap (λ p → loop ∙ p) (!-inv-l loop) ⟩
           loop ∙ refl _
         ≡⟨ refl _ ⟩
           loop ∎

-- Q: Is loop distinct from refl?
-- A: so far, maybe - so far its consistent that loop is refl,
-- also consistent that its not
-- spoiler: we need the elimination principle for S1 and
-- univalence

-- Circle recursion
postulate
  S1-rec : {X : Type} (x : X) (l : x ≡ x) → S1 → X
  -- reduction rule for S1-rec
  S1-rec-base : {X : Type} (x : X) (l : x ≡ x) → (S1-rec x l) base ≡ x

-- Allow S1-rec-base to be used to automatically rewrite, since it should be a def. equality anyway

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE S1-rec-base #-}

-- the rewrite allows us to define the action of S1-rec on loop:

postulate
  S1-rec-loop : {X : Type} (x : X) (l : x ≡ x) → ap (S1-rec x l) loop ≡ l

-- example

double : S1 → S1
double = S1-rec base (loop ∙ loop)

double-loop : ap double loop ≡ loop ∙ loop
double-loop = S1-rec-loop base (loop ∙ loop)

postulate
  Circle2 : Type
  north : Circle2
  south : Circle2
  west : north ≡ south
  east : north ≡ south
  Circle2-rec : {X : Type} (n s : X) (w e : n ≡ s) → Circle2 → X
  Circle2-rec-n : {X : Type} (n s : X) (w e : n ≡ s) → Circle2-rec n s w e north ≡ n
  Circle2-rec-s : {X : Type} (n s : X) (w e : n ≡ s) → Circle2-rec n s w e south ≡ s

{-# REWRITE Circle2-rec-n #-}
{-# REWRITE Circle2-rec-s #-}

to : S1 → Circle2
to = S1-rec north (east ∙ ! west)

from : Circle2 → S1
from = Circle2-rec base base (refl _) loop



```
