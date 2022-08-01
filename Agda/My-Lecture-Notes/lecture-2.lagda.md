
```agda

{-# OPTIONS --without-K --safe #-}

module lecture-2 where

open import lecture1 hiding (𝟘 ; 𝟙 ; D)

```

The topic today is about defining all the logical connectives of MLTT in Agda.

```agda
-- The empty type
data 𝟘 : Type where

-- the induction principle for 𝟘
𝟘-elim : {A : 𝟘 → Type} (x : 𝟘) → A x
𝟘-elim ()

¬_ : Type → Type
¬ A = A → 𝟘

𝟘-nondep-elim : {B : Type} → 𝟘 → B
𝟘-nondep-elim {B} = 𝟘-elim {λ _ → B}

```

Mostly stuff I already know, so will not take much notes

M-. go to definition 
M-, go back to the previous location
These two commands work like a stack, being push and pop respectively.

C-x 2 opens the current buffer in a new frame split horizontally
C-x 3 opens the current buffer in a new frame split vertically

C-u C-x = lookup how to type a symbol in agda-mode

C-c C-, show goal and context

Record definitions satisfy η rule, unlike general inductive defs

```agda
record 𝟙 : Type where
  constructor ⋆

data 𝟙' : Type where
  ⋆ : 𝟙'

-- Now to define the following induction principle, we need to pattern match:

𝟙'-elim : {A : 𝟙' → Type} → A ⋆ → (x : 𝟙') → A x
𝟙'-elim a ⋆ = a

-- but not the induction principle for the record type, due to the η rule

𝟙-elim : {A : 𝟙 → Type} → A ⋆ → (x : 𝟙) → A x
𝟙-elim a x = a


record ≡ {A : Type} (a : A) : A → Type where
  constructor refl_
  field
    b : A
```

∥ A ∔ B ∥ truncates proofs of A ∔ B so they are all equal. 
