```agda
{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import new-prelude
open import Lecture4-notes

module My-exercises4 where
```

# Constructing homotopies between paths

(⋆) Give two "different" path-between-paths/homotopies between (loop ∙ !
loop) ∙ loop and loop.  They should be different in the sense that one
should cancel the !loop with the first loop, and one with the second
loop.  But these aren't really *really* different, in that there will be
a path-between-paths-between-paths between the two!  

```agda
homotopy1 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy1 = (loop ∙ ! loop) ∙ loop
          ≡⟨ ap (λ p → p ∙ loop) (!-inv-r loop) ⟩
            refl _ ∙ loop
          ≡⟨ ∙unit-l loop ⟩
            loop ∎

homotopy2 : (loop ∙ ! loop) ∙ loop ≡ loop
homotopy2 = (loop ∙ ! loop) ∙ loop
          ≡⟨ ! (∙assoc loop (! loop) loop) ⟩
            loop ∙ (! loop ∙ loop)
          ≡⟨ ap (λ p → loop ∙ p) (!-inv-l loop) ⟩
            loop ∙ (refl _)
          ≡⟨ refl loop ⟩
            loop ∎
```

(Harder exercise (🌶️): give a path between homotopy1 and
homotopy2! I'd recommend saving this until later though, because there
is a trick to it that we haven't covered in lecture yet.)

```agda
path-between-paths-between-paths : homotopy1 ≡ homotopy2
path-between-paths-between-paths =
    ap (λ p → p ∙ loop) (!-inv-r loop) ∙ ∙unit-l loop
  ≡⟨ {!!} ⟩
    ! (∙assoc loop (! loop) loop) ∙ ap (_∙_ loop) (!-inv-l loop)
  ∎
```

# Functions are group homomorphism 

(⋆⋆) State and prove a general lemma about what ap of a function on the
inverse of a path (! p) does (see ap-∙ for inspiration).  

State and prove a general lemma about what ! (p ∙ q) is.  

Use them to prove that the double function takes loop-inverse to
loop-inverse concatenated with itself.

```agda

ap-inverse : {A B : Type} {x y : A} {f : A → B} (p : x ≡ y) → ap f (! p) ≡ ! (ap f p) [ (f y ≡ f x) ]
ap-inverse {A} {B} {x} {.x} {f} (refl .x) = refl (refl (f x))

ap-distr-∙ : {A B : Type} {x y z : A} {f : A → B} (p : x ≡ y) (q : y ≡ z) → ap f (p ∙ q) ≡ ap f p ∙ ap f q
ap-distr-∙ {A} {B} {x} {y} {.y} {f} p (refl .y) = refl (ap f p)

distr-!-∙ : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ! (p ∙ q) ≡ ! q ∙ ! p [ z ≡ x ]
distr-!-∙ {A} {x} {.x} {.x} (refl .x) (refl .x) = refl (refl x)

double-!loop : ap double (! loop) ≡ ! loop ∙ ! loop
double-!loop = ap-inverse loop ∙
               (ap ! (S1-rec-loop base (loop ∙ loop))
                     ∙ distr-!-∙ loop loop)
```

(⋆) Define a function invert : S1 → S1 such that (ap invert) inverts a path
on the circle, i.e. sends the n-fold loop to the -n-fold loop.  

```agda
invert : S1 → S1
invert c = S1-rec base (! loop) c
```

# Circles equivalence

See the maps between the 1 point circle and the 2 point circle in the
lecture code.  Check that the composite map S1 → S1
is homotopic to the identity on base and loop:

(⋆)

For reference:

```agda
-- to : S1 → Circle2
-- to = S1-rec north (east ∙ ! west)

-- from : Circle2 → S1
-- from = Circle2-rec base base (refl base) loop
```

```agda
to-from-base : from (to base) ≡ base
to-from-base = refl _
```

(⋆⋆⋆) 

```
to-from-loop : ap from (ap to loop) ≡ loop
to-from-loop =
  ap from (ap to loop)
  ≡⟨ ap (λ p → ap from p)
     (S1-rec-loop north (east ∙ ! west)) ⟩
  ap from (east ∙ ! west)
  ≡⟨ ap-distr-∙ east (! west) ⟩
  ap from east ∙ ap from (! west)
  ≡⟨ ap (λ p → ap from east ∙ p)
     (ap-inverse west) ⟩
  ap from east ∙ ! (ap from west)
  ≡⟨ ap (λ p → p ∙ ! (ap from west))
     (Circle2-rec-east base base (refl base) loop) ⟩
  loop ∙ ! (ap from west)
  ≡⟨ ap (λ p → loop ∙ ! p)
     (Circle2-rec-west base base (refl base) loop) ⟩
  loop ∙ ! (refl base)
  ≡⟨ refl loop ⟩
  loop ∙ refl base
  ≡⟨ refl loop ⟩
  loop ∎

```

Note: the problems below here are progressively more optional, so if you
run out of time/energy at some point that is totally fine.  

# Torus to circles

The torus is equivalent to the product of two circles S1 × S1.  The idea
for the map from the torus to S1 × S1 that is part of this equivalence
is that one loop on on the torus is sent to to the circle loop in one
copy of S1, and the other loop on the torus to the loop in the other
copy of the circle.  Define this map.  

Hint: for the image of the square, you might want a lemma saying how
paths in product types compose (⋆⋆⋆):

```agda
compose-pair≡ : {A B : Type} {x1 x2 x3 : A} {y1 y2 y3 : B}
                (p12 : x1 ≡ x2) (p23 : x2 ≡ x3)
                (q12 : y1 ≡ y2) (q23 : y2 ≡ y3)
              → ((pair≡ p12 q12) ∙ (pair≡ p23 q23))
              ≡ pair≡ (p12 ∙ p23) (q12 ∙ q23)
                [ (x1 , y1) ≡ (x3 , y3) [ A × B ] ]
compose-pair≡ {A} {B} {x1} {.x1} {.x1} {y1} {.y1} {.y1} (refl .x1) (refl .x1) (refl .y1) (refl .y1) = refl (refl (x1 , y1))
```

(🌶️)
```
torus-to-circles : Torus → S1 × S1
torus-to-circles =
  T-rec (base , base)
    (pair≡ loop (refl _))
    (pair≡ (refl _) loop)
    path-between-paths
  where

    path-between-paths : pair≡ loop (refl base)
                         ∙ pair≡ (refl base) loop
                       ≡ pair≡ (refl base) loop
                         ∙ pair≡ loop (refl base)
    path-between-paths =
      pair≡ loop (refl base) ∙ pair≡ (refl base) loop
      ≡⟨ compose-pair≡ loop (refl base) (refl base) loop ⟩
      pair≡ (loop ∙ refl base) (refl base ∙ loop)
      ≡⟨ ap (λ p → pair≡ p (refl base ∙ loop))
         (! (∙unit-l loop)) ⟩
      pair≡ (refl base ∙ loop) (refl base ∙ loop)
      ≡⟨ ap (λ p → pair≡ (refl base ∙ loop) p)
         (∙unit-l loop) ⟩
      pair≡ (refl base ∙ loop) (loop ∙ refl base)
      ≡⟨ ! (compose-pair≡ (refl base) loop loop (refl base)) ⟩
      pair≡ (refl base) loop ∙ pair≡ loop (refl base) ∎
```

# Suspensions (🌶️)

Find a type X such that the two-point circle Circle2 is equivalent to
the suspension Susp X.  Check your answer by defining a logical
equivalence (functions back and forth), since we haven't seen how to
prove that such functions are inverse yet.

```agda
c2s : Circle2 → Susp Bool
c2s = Circle2-rec northS southS (merid false) (merid true)

s2c : Susp Bool → Circle2
s2c = Susp-rec north south go
  where
    go : Bool → north ≡ south
    go true = east
    go false = west

```

Suspension is a functor from types, which means that it acts on
functions as well as types.  Define the action of Susp on functions:

```agda
susp-func : {X Y : Type} → (f : X → Y) → Susp X → Susp Y
susp-func f = Susp-rec northS southS (λ x → merid (f x)) 
```

To really prove that Susp is a functor, we should check that this action
on functions preserves the identity function and composition of
functions. But to do that we would need the dependent elimination rule
for suspensions, which we haven't talked about yet.

# Pushouts (🌶️)

Fix a type X.  Find types A,B,C with functions f : C → A and g : C → B
such that the suspension Susp X is equivalent to the Pushout C A B f g.
Check your answer by defining a logical equivalence (functions back and
forth), since we haven't seen how to prove that such functions are
inverse yet.

```agda
SuspFromPush : Type → Type
SuspFromPush A = Pushout A 𝟙 𝟙 (λ _ → ⋆) (λ _ → ⋆)

s2p : (A : Type) → Susp A → SuspFromPush A
s2p A = Susp-rec (inl ⋆) (inr ⋆) glue

p2s : (A : Type) → SuspFromPush A → Susp A
p2s A = Push-rec (λ _ → northS) (λ _ → southS) merid

s2p∘p2s : (A : Type) (x : 𝟙) → s2p A (p2s A (inl x)) ≡ inl x
s2p∘p2s A ⋆ = {!!} -- can't prove this yet, but clearly it holds
-- Similarly goes for inr x

p2s∘s2p : (A : Type) (x : 𝟙) → p2s A (s2p A (northS)) ≡ northS
p2s∘s2p = {!!} -- also obvious, similarly goes for southS


```

