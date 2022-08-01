```agda
{-# OPTIONS --rewriting --without-K #-}

open import new-prelude

module My-lecture5-live where

open import Lecture4-notes hiding (to; from; from-to-north; from-to-south; from-to-west; from-to-east; q) public

record is-equiv {l1 l2 : Level} {A : Type l1} {B : Type l2} (f : A → B) : Type (l1 ⊔ l2) where

record _≃_ {l1 l2 : Level} (A : Type l1) (B : Type l2) : Type (l1 ⊔ l2) where
  constructor
    Equivalence
  field
    map : A → B
    is-equivalence : is-equiv map

fwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → A → B
fwd e = _≃_.map e

bwd : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≃ B → B → A
bwd e = {!_≃_.is-equival !}

improve : ∀ {l1 l2 : Level} {A : Type l1} {B : Type l2} → A ≅ B → A ≃ B
improve (Isomorphism f (Inverse g gf fg)) = {!!}

-- We need a new concept to state the dependent elimination principle for HITs.

data PathOver {l1 l2 : Level} {A : Type l1} (B : A → Type l2) :
              {a1 a2 : A} (p : a1 ≡ a2)
              (b1 : B a1) (b2 : B a2) → Type (l1 ⊔ l2) where
-- now we want to ask whether b1 ≡ b2, but we can't because they have different types... so can't typecheck b1 ≡ b2 [ B a2 ]
-- we can however talk about paths p : (a1, b1) ≡ (a2, b2) [ Σ x : A , B x]
-- The path p lives "over" the path `ap pr₁ p : a1 ≡ a2`.
-- We also have `transport (ap pr₁ p) b1` which has the type ` B a2`, i.e. the fiber "over" a2. This is also where b2 lives.
-- We define a type that is equivalent to this cumbersome way of working with transport.

   reflo : {x : A} {y : B x} → PathOver B (refl x) y y

syntax PathOver B p b1 b2 = b1 ≡ b2 [ B ↓ p ] -- heterogenous equality up to p, or "over" p

transport-to-pathover : {l1 l2 : Level} {A : Type l1} (B : A → Type l2)
                        {a1 a2 : A} (p : a1 ≡ a2)
                        (b1 : B a1) (b2 : B a2)
                     → (transport B p b1 ≡ b2) ≃ (b1 ≡ b2 [ B ↓ p ]) 
transport-to-pathover B (refl _) b1 b2 =
  Equivalence {!λ!}
    {!Isomorphism!}

path-to-pathover : ∀ {A : Type} {B : A → Type}
                 → {a : A} {x y : B a}
                 → (p : x ≡ y)
                 → x ≡ y [ B ↓ refl a ]
path-to-pathover p = {!!}

apd : {l1 l2 : Level} {A : Type l1} {B : A → Type l2}
      (f : (x : A) → B x) {a1 a2 : A} (p : a1 ≡ a2)
    → {!!}
apd = {!!}

postulate
  Circle2-elim : (X : Circle2 → Type)
                 (n : {!!})
                 (s : {!!})
                 (w : {!!})
                 (e : {!!})
               → (x : Circle2) → X x
{-
  Circle2-elim-north : (X : Circle2 → Type) (n : X north) (s : X south)
                       (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e north ≡ {!!}
  Circle2-elim-south : (X : Circle2 → Type) (n : X north) (s : X south)
                       (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                     → Circle2-elim X n s w e south ≡ {!!}
-- {-# REWRITE Circle2-elim-north #-}
-- {-# REWRITE Circle2-elim-south #-}
postulate
  Circle2-elim-west : (X : Circle2 → Type) (n : X north) (s : X south)
                      (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                    → apd (Circle2-elim X n s w e) west ≡ {!!}
  Circle2-elim-east : (X : Circle2 → Type) (n : X north) (s : X south)
                      (w : n ≡ s [ X ↓ west ]) (e : n ≡ s [ X ↓ east ])
                    → apd (Circle2-elim X n s w e) east ≡ {!!}
-}

module RememberTheseFromLastTime where

  to : S1 → Circle2
  to = S1-rec north (east ∙ ! west)
  
  from : Circle2 → S1
  from = Circle2-rec base base (refl base) loop
  
  from-to-north : to (from north) ≡ north
  from-to-north = {!!}
  
  from-to-south : to (from south) ≡ south
  from-to-south = {!!}
  
  from-to-west : ap to (ap from west) ∙ from-to-south ≡ west
  from-to-west =  ap to (ap from west) ∙ from-to-south ≡⟨ {!!} ⟩
                  ap to (refl base) ∙ from-to-south  ≡⟨ {!!} ⟩
                  west ∎  
  
  from-to-east : ap to (ap from east) ∙ from-to-south ≡ east
  from-to-east =  ap to (ap from east) ∙ from-to-south ≡⟨ ap (\ H → ap to H ∙ from-to-south) (Circle2-rec-east _ _ _ _) ⟩
                  ap to loop           ∙ from-to-south ≡⟨ ap (\ H → H ∙ from-to-south) (S1-rec-loop _ _) ⟩
                  east ∙ ! west        ∙ from-to-south ≡⟨ ! (∙assoc _ (! west) from-to-south) ⟩
                  east ∙ (! west ∙ from-to-south)      ≡⟨ ap (\ H → east ∙ H) {!!} ⟩
                  east ∎ 
                    
open RememberTheseFromLastTime public

from-to : (y : Circle2) → to (from y) ≡ y
from-to = {!!}

postulate
  S1-elim : (X : S1 → Type)
            (x : {!!})
            (p : {!!})
          → (x : S1) → X x

{-
  S1-elim-base : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → S1-elim X x p base ≡ ?

{-# REWRITE S1-elim-base #-}
postulate
  S1-elim-loop : (X : S1 → Type)
                 (x : X base)
                 (p : x ≡ x [ X ↓ loop ])
               → apd (S1-elim X x p) loop ≡ ?
-}

PathOver-path-loop : ∀ {A : Type} 
                     {a a' : A} {p : a ≡ a'}
                     {q : a ≡ a}
                     {r : a' ≡ a'}
                   → {!!}
                   → {!!}
PathOver-path-loop = {!!}

mult : S1 → S1 → S1
mult = {!!} 

```
