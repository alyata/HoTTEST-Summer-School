# Week 02 - Agda Exercises

## Please read before starting the exercises

**The exercises are designed to increase in difficulty so that we can cater to
our large and diverse audience. This also means that it is *perfectly fine* if
you don't manage to do all exercises: some of them are definitely a bit hard for
beginners and there are likely too many exercises! You *may* wish to come back
to them later when you have learned more.**

Having said that, here we go!

This is a markdown file with Agda code, which means that it displays nicely on
GitHub, but at the same time you can load this file in Agda and fill the holes
to solve exercises.

**Please make a copy of this file to work in, so that it doesn't get overwritten
  (in case we update the exercises through `git`)!**

```agda
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 02-Exercises where

open import prelude
open import decidability
open import sums
open import empty-type
```

## Part I: Propositions as types


### Exercise 1 (★)

Prove
```agda
uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
uncurry f (a , b) = f a b

curry : {A B X : Type} → (A × B → X) → (A → B → X)
curry f a b = f (a , b)
```
You might know these functions from programming e.g. in Haskell.
But what do they say under the propositions-as-types interpretation?


### Exercise 2 (★)

Consider the following goals:
```agda
[i] : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
[i] = {!!}

[ii] : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
[ii] = {!!}

[iii] : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
[iii] = {!!}

[iv] : {A B : Type} → ¬ (A × B) → ¬ A ∔ ¬ B
[iv] = {!!}

[v] : {A B : Type} → (A → B) → ¬ B → ¬ A
[v] = {!!}

[vi] : {A B : Type} → (¬ A → ¬ B) → B → A
[vi] = {!!}

[vii] : {A B : Type} → ((A → B) → A) → A
[vii] = {!!}

[viii] : {A : Type} {B : A → Type}
    → ¬ (Σ a ꞉ A , B a) → (a : A) → ¬ B a
[viii] = {!!}

[ix] : {A : Type} {B : A → Type}
    → ¬ ((a : A) → B a) → (Σ a ꞉ A , ¬ B a)
[ix] = {!!}

[x] : {A B : Type} {C : A → B → Type}
      → ((a : A) → (Σ b ꞉ B , C a b))
      → Σ f ꞉ (A → B) , ((a : A) → C a (f a))
[x] = {!!}
```
For each goal determine whether it is provable or not.
If it is, fill it. If not, explain why it shouldn't be possible.
Propositions-as-types might help.


### Exercise 3 (★★)

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```
In the lecture we have discussed that we can't  prove `∀ {A : Type} → ¬¬ A → A`.
What you can prove however, is
```agda
tne : ∀ {A : Type} → ¬¬¬ A → ¬ A
tne {A} nnna a = nnna (λ na → na a)
```


### Exercise 4 (★★★)
Prove
```agda
¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
¬¬-functor f nna nb = nna (λ a → nb (f a))

¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
¬¬-kleisli f nna nb = nna (λ a → f a nb)
```
Hint: For the second goal use `tne` from the previous exercise





## Part II: `_≡_` for `Bool`

**In this exercise we want to investigate what equality of booleans looks like.
In particular we want to show that for `true false : Bool` we have `true ≢ false`.**

### Exercise 1 (★)

Under the propositions-as-types paradigm, an inhabited type corresponds
to a true proposition while an uninhabited type corresponds to a false proposition.
With this in mind construct a family
```agda
bool-as-type : Bool → Type
bool-as-type true = 𝟙
bool-as-type false = 𝟘
```
such that `bool-as-type true` corresponds to "true" and
`bool-as-type false` corresponds to "false". (Hint:
we have seen canonical types corresponding true and false in the lectures)

### Exercise 2 (★★)

Prove
```agda
bool-≡-char₁ : ∀ (b b' : Bool) → b ≡ b' → (bool-as-type b ⇔ bool-as-type b')
bool-≡-char₁ true true x = (λ y → y) , λ y → y
bool-≡-char₁ false false x = (λ y → y) , λ y → y
```

### Exercise 3 (★★)

Using ex. 2, concldude that
```agda
true≢false : ¬ (true ≡ false)
true≢false x = pr₁ (bool-≡-char₁ true false x) ⋆
```
You can actually prove this much easier! How?

```agda
true≢false' : ¬ (true ≡ false)
true≢false' ()

false≢true : ¬ (false ≡ true)
false≢true ()
```

### Exercise 4 (★★★)

Finish our characterisation of `_≡_` by proving
```agda
bool-≡-char₂ : ∀ (b b' : Bool) → (bool-as-type b ⇔ bool-as-type b') → b ≡ b'
bool-≡-char₂ true true x = refl _
bool-≡-char₂ true false x with pr₁ x ⋆
...                       | ()
bool-≡-char₂ false true x with pr₂ x ⋆
...                       | ()
bool-≡-char₂ false false x = refl _
```


## Part III (🌶)
A type `A` is called *discrete* if it has decidable equality.
Consider the following predicate on types:
```agda
has-bool-dec-fct : Type → Type
has-bool-dec-fct A = Σ f ꞉ (A → A → Bool) , (∀ x y → x ≡ y ⇔ (f x y) ≡ true)
```

Prove that

```agda
decidable-equality-char : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
<<<<<<< Updated upstream
decidable-equality-char = ?
=======
decidable-equality-char A = l-to-r , r-to-l
  where
    l-to-r : has-decidable-equality A → has-bool-dec-fct A
    l-to-r h = f , p
      where
        -- define f s.t. using the decidability of a ≡ b,
        -- if a ≡ b then return true
        --          else return false
        f : A → A → Bool
        f a b with h a b
        ...   | inl _ = true
        ...   | inr _ = false
        
        p : ∀ x y → x ≡ y ⇔ (f x y) ≡ true
        p x y = p-l-to-r , p-r-to-l
          where
            -- we prove both directions by cases on whether x ≡ y or not
            -- In both directions, we obtain a contradiction in the case ¬ x ≡ y.
            p-l-to-r : x ≡ y → (f x y) ≡ true
            p-l-to-r x≡y with h x y
            ...        | inl _ = refl _ -- if x ≡ y then f x y computes to true
            ...        | inr ¬x≡y = 𝟘-elim (¬x≡y x≡y)
            p-r-to-l : (f x y) ≡ true → x ≡ y
            p-r-to-l fxy≡true with h x y
            ...        | inl x≡y  = x≡y
            ...        | inr ¬x≡y = 𝟘-elim (false≢true fxy≡true)
    r-to-l : has-bool-dec-fct A → has-decidable-equality A
    r-to-l (f , hf) x y with hf x y
    ...                 | hfxy with f x y
    ...                        | true = inl (pr₂ (hfxy) (refl _))
    ...                        | false = inr (λ x≡y → false≢true (pr₁ hfxy x≡y))

decidable-equality-char' : (A : Type) → has-decidable-equality A ⇔ has-bool-dec-fct A
decidable-equality-char' A = l-to-r , r-to-l
  where
    l-to-r : has-decidable-equality A → has-bool-dec-fct A
    l-to-r dec-eq = f , p
      where
        -- define f s.t. using the decidability of a ≡ b,
        -- if a ≡ b then return true
        --          else return false
        -- We have to take the decidability as an argument so
        -- that we can prove the property p without using a
        -- with-abstraction.

        f' : (a : A) → (b : A) → is-decidable (a ≡ b) → Bool
        f' a b (inl _) = true
        f' a b (inr _) = false
        
        f : A → A → Bool
        f a b = f' a b (dec-eq a b)
        
        p : ∀ x y → x ≡ y ⇔ (f' x y (dec-eq x y)) ≡ true
        p x y = p-l-to-r , {!!} -- p-r-to-l
          where
            -- we prove both directions by cases on whether x ≡ y or not
            -- In both directions, we obtain a contradiction in the case ¬ x ≡ y.
            p-l-to-r : x ≡ y → (f' x y (dec-eq x y)) ≡ true
            p-l-to-r x≡y = helper (dec-eq x y)
             where
              helper : (dec : is-decidable (x ≡ y)) → (f' x y dec) ≡ true
              helper (inl _) = refl _ -- if x ≡ y then f x y computes to true
              helper (inr ¬x≡y) = 𝟘-elim (¬x≡y x≡y)
            
            p-r-to-l : (f' x y (dec-eq x y)) ≡ true → x ≡ y
            p-r-to-l = helper (dec-eq x y)
             where
              -- helper has to take in the other argument as
              -- well since we are pattern matching on
              -- `dec-eq x y` which occurs in that argument.
              helper : (dec : is-decidable (x ≡ y)) →
                       (f' x y dec) ≡ true → x ≡ y
              helper (inl x≡y) _         = x≡y
              helper (inr ¬x≡y) fxy≡true = 𝟘-elim (false≢true fxy≡true)
    r-to-l : has-bool-dec-fct A → has-decidable-equality A
    r-to-l (f , hf) x y = helper (f x y) (hf x y)
      where
        helper : (b : Bool) → x ≡ y ⇔ b ≡ true → is-decidable (x ≡ y) --(x ≡ y ⇔ (f x y) ≡ true)
        helper true hfxy = inl (pr₂ (hfxy) (refl _))
        helper false hfxy = inr {!λ x≡y → false≢true (pr₁ hfxy x≡y)!}
-- with hf x y
--     ...                 | hfxy with f x y
--     ...                        | true = inl (pr₂ (hfxy) (refl _))
--     ...                        | false = inr (λ x≡y → false≢true (pr₁ hfxy x≡y))
```
