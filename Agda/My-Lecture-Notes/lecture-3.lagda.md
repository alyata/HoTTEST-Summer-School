

```agda
{-# OPTIONS --without-K --safe #-}

module lecture-3 where

open import prelude

transs : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transs p (refl _) = p

transss : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
transss (refl _) (refl _) = refl _


```

Generalise definitions to arbitrary universe levels

```agda
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
                           renaming (Set to 𝓤)
                           public
```

Let i, j, k be universe levels.

```agda
variable i j k : Level
```

We can define a universe-polymorphic version of Sigma types

```agda
record S (A : 𝓤 i) (B  : A → 𝓤 j) : 𝓤 (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : B pr₁ 
```

variables become implicit arguments to any definitions in its scope.

```agda
σ : (A : 𝓤 i) (B : A → 𝓤 j) → 𝓤 (i ⊔ j)
σ {i} {j} A B = S {i} {j} A B
```

We truncate to obtain a mere proposition when attempting to use types as propositions.

Example: composite numbers

```agda
-- CN : 𝓤
-- CN = Σ x : ℕ, Σ (y, z) ꞉ ℕ × ℕ , x ≡ y * z
```

```agda

```
