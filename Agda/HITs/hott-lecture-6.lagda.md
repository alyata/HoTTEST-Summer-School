```agda
{-# OPTIONS --without-K #-}

module hott-lecture-6 where

open import new-prelude

record is-equiv 

```

The goal in this file is to formalise the constructions and proofs from lecture 6 of HoTT. The constructions we are interested in are

- def: contractible types
- def: contractible maps
- proof: equivalences are contractible maps
-   we use the intermediate notion of coherently inveritble maps

```agda

-- A type `A` is contractible if there exists a center of contraction `c : A` for which every inhabitant of A is equal to. The contraction is the `(x : A) → c ≡ x`, which we can also describe as the homotopy const c ∼ id.
is-contr : Type → Type
is-contr A = Σ c ꞉ A , ((x : A) → c ≡ x)

-- An observation: a type `A` is contractible iff `const ⋆ : A → 𝟙` is an equivalence.

equiv-of-contr : (A : Type) → is-contr A → is-equiv (const ⋆)
equiv-of-contr A (c, C) = ?

```
