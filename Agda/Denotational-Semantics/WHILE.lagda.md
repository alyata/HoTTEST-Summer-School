
```agda

{-# OPTIONS --without-K --safe #-}

module WHILE where

open import general-notation using (Type; _$_)
open import natural-numbers-type using (ℕ; zero; suc; _+_; _*_)
open import Bool using (Bool; true; false; _&&_; if_then_else_)
open import unit-type using (𝟙; ⋆)
open import binary-sums using (_∔_; inl; inr; ∔-elim)
open import identity-type using (_≡_; refl; trans; sym)
open import empty-type using (¬_)
open import sums using (Sigma; Σ; pr₁; pr₂; _,_)
open import function-extensionality using (FunExt)

```

Let us begin by defining the data structures representing the WHILE language.

```agda
module inside (𝕍 : Type) where
  data WHILE-ℕ : Type where
    ~_   : ℕ → WHILE-ℕ      -- literal
    _++_ : WHILE-ℕ → WHILE-ℕ → WHILE-ℕ  -- addition
    _××_ : WHILE-ℕ → WHILE-ℕ → WHILE-ℕ  -- multiplication
    v_   : 𝕍 → WHILE-ℕ      -- variable
    -- and we can have other stuff but that's besides the point
  
  data WHILE-𝔹 : Type where
    tt ff : WHILE-𝔹                      -- literal
    _≫_   : WHILE-ℕ → WHILE-ℕ → WHILE-𝔹  -- greater than
    _∧_   : WHILE-𝔹 → WHILE-𝔹 → WHILE-𝔹  -- conjunction

  data WHILE-Command : Type where
    _≔_ : 𝕍 → WHILE-ℕ → WHILE-Command -- variable assignment
    If_Then_Else_ : WHILE-𝔹 → WHILE-Command → WHILE-Command → WHILE-Command
    While_Do_ : WHILE-𝔹 → WHILE-Command → WHILE-Command 
    _∘_ : WHILE-Command → WHILE-Command → WHILE-Command -- composition
    Skip : WHILE-Command
```

The domain of denotation for WHILE-ℕ and WHILE-𝔹 will be a function from states
to natural numbers/booleans in agda. States are variable stores: functions from 𝕍
to ℕ. For commands, it will be a partial function from state to state.

```agda
  State : Type
  State = 𝕍 → ℕ

  𝔻-ℕ : Type
  𝔻-ℕ = State → ℕ

  𝔻-𝔹 : Type
  𝔻-𝔹 = State → Bool

  𝔻-Command : Type
  𝔻-Command = State → State ∔ 𝟙 -- A unit output means the function is undefined

  _>>>_ : 𝔻-Command → 𝔻-Command → 𝔻-Command
  (f >>> g) s with (f s)
  ...            | inl s' = g s'
  ...            | inr ⋆ = inr ⋆
```

Now, we can begin to consider the domain theory of 𝔻-Command. First, we construct
the information ordering on 𝔻-Command, showing that
  1. The relation ⊑ is indeed a partial order relation.
  2. There is a least element ⊥.
  3. Every chain w₁ ⊑ w₂ ... has a least-upper bound ⨆ wᵢ.
  
```agda

  -- The partial order on 𝔻-Command: g agrees with f for every input x where f is
  -- defined
  _⊑_ : 𝔻-Command → 𝔻-Command → Type
  f ⊑ g = (x : State) → (Σ y ꞉ State , f x ≡ inl y) → f x ≡ g x

  infix 0 _⊑_

  -- This relation is indeed a partial order
  ⊑-reflexive : (f : 𝔻-Command) → f ⊑ f
  ⊑-reflexive f x hx = refl _
  
  -- Without function extensionality, we say f x = g x for all x instead of f = g
  -- i.e. pointwise equality. We will assume funext when we need it to develop
  -- the general domain theory of 𝔻­Command
  ⊑-antisymm : {f g : 𝔻-Command} → f ⊑ g → g ⊑ f → ((x : State) → f x ≡ g x)
  ⊑-antisymm {f} {g} hfg hgf x = helper (f x) (g x) (hfg x) (hgf x) 
    where
      hfg' = hfg x
      hgf' = hgf x

      -- idea: we should case split
      -- if f x is defined then by hfg, f x = g x
      -- else if g x is defined then by hgf, f x = g x
      -- else both are undefined again f x = g x = inr ⋆
      helper : (fx gx : State ∔ 𝟙) →
               ((Σ y₁ ꞉ State , fx ≡ inl y₁) → fx ≡ gx) →
               ((Σ y₂ ꞉ State , gx ≡ inl y₂) → gx ≡ fx) →
               fx ≡ gx
      helper (inl fy) gy hfx hgx = hfx (fy , refl _)
      helper (inr ⋆) (inl gy) hfx hgx = sym (hgx (gy , refl _))
      helper (inr ⋆) (inr ⋆) hfx hgx = refl _

  ⊑-trans : (f g h : 𝔻-Command) → f ⊑ g → g ⊑ h → f ⊑ h
  ⊑-trans f g h f⊑g g⊑h x hf = trans fx≡gx gx≡hx
    where
      -- first of all, hf only depends on f, so it is the same as the premise of f⊑g
      -- hence we can use it to obtain f x = g x
      fx≡gx : f x ≡ g x
      fx≡gx = f⊑g x hf

      gx≡hx : g x ≡ h x
      gx≡hx = g⊑h x (pr₁ hf , trans (sym fx≡gx) (pr₂ hf))
  
  -- The least element is the empty function
  ⊥ : 𝔻-Command
  ⊥ _ = inr ⋆

  ⊥-least : (f : 𝔻-Command) → ⊥ ⊑ f
  ⊥-least f x (y , ())
```

We will need to describe the construction of chains in 𝔻-Command. We describe them
as infinite sequences for which wᵢ ⊑ wᵢ₊₁.

```agda
  Chain : Type
  Chain = Σ seq ꞉ (ℕ → 𝔻-Command) , ((i : ℕ) → seq i ⊑ seq (suc i))

  -- Every chain has an upper bound, which is defined on x precisely when any of the
  -- functions in the chain is defined on x.
  ⨆ : Chain → 𝔻-Command
  ⨆ (seq , order) x = {!!}

  _ub-of_ : 𝔻-Command → Chain → Type
  ub ub-of (seq , _) = (i : ℕ) → (seq i) ⊑ ub

  ⨆-ub : (chain : Chain) → (⨆ chain) ub-of chain
  ⨆-ub = {!!}

  ⨆-lub : (chain : Chain) → (ub : 𝔻-Command) → ub ub-of chain → (⨆ chain) ⊑ ub 
  ⨆-lub = {!!}
```

Now, a particular chain is constructed by applying a monotonic, continuous function
to ⊥ repeatedly.

```agda

  Monotonic : (f : 𝔻-Command → 𝔻-Command) → Type
  Monotonic f = {x y : 𝔻-Command} → x ⊑ y → f x ⊑ f y

  _<$>[_]_ : (f : 𝔻-Command → 𝔻-Command) → (Monotonic f) → Chain → Chain
  f <$>[ mono ] (seq , order) = (λ i → f (seq i)) , λ i → mono (order i)

  Continuous : (f : 𝔻-Command → 𝔻-Command) (mono : Monotonic f) → Type
  Continuous f mono = (chain : Chain) → f (⨆ chain) ≡ ⨆ (f <$>[ mono ] chain)

  chain-of : (f : 𝔻-Command → 𝔻-Command) →
             (mono : Monotonic f) → (cont : Continuous f mono) →
             Chain
  chain-of f mono cont = seq , order
    where
      seq : ℕ → 𝔻-Command
      seq zero = ⊥
      seq (suc i) = f (seq i)

      order : (i : ℕ) → seq i ⊑ f (seq i)
      order 0 = ⊥-least _
      order (suc i) = mono (order i)

  _is-fixpoint-of_ : (fix : 𝔻-Command) → (f : 𝔻-Command → 𝔻-Command) → Type
  fix is-fixpoint-of f = f fix ≡ fix

  lub-is-fixpoint : (funext : FunExt) →
                    (f : 𝔻-Command → 𝔻-Command) →
                    (mono : Monotonic f) → (cont : Continuous f mono) →
                    (⨆ (chain-of f mono cont)) is-fixpoint-of f
  lub-is-fixpoint funext f mono cont = trans cont' tail-irrelevant
    where
      -- First, we put the f inside the ⨆
      cont' : f (⨆ (chain-of f mono cont))
            ≡ ⨆ (f <$>[ mono ] (chain-of f mono cont))
      cont' = cont (chain-of f mono cont)

      -- Then, we establish that removing the first term from the chain does not
      -- change its lub. We do this by using anti-symmetry (and to use that we
      -- need funext). We prove that both lubs are ubs of each other. so they
      -- are less than or equal to each other under the information ordering.

      left-ub : ⨆ (f <$>[ mono ] (chain-of f mono cont)) ub-of
                (chain-of f mono cont)
      left-ub i x (y , h) = {!!} -- need to define ⨆ first

      right⊑left : ⨆ (chain-of f mono cont) ⊑
                   ⨆ (f <$>[ mono ] (chain-of f mono cont))
      right⊑left = ⨆-lub (chain-of f mono cont) _ left-ub

      right-ub : ⨆ (chain-of f mono cont) ub-of
                 (f <$>[ mono ] (chain-of f mono cont))
      right-ub i x (y , h) = {!!} -- need to define ⨆ first

      left⊑right : ⨆ (f <$>[ mono ] (chain-of f mono cont)) ⊑
                   ⨆ (chain-of f mono cont)
                   
      left⊑right = ⨆-lub (f <$>[ mono ] (chain-of f mono cont)) _ right-ub
      
      tail-irrelevant : ⨆ (f <$>[ mono ] (chain-of f mono cont))
                      ≡ ⨆ (chain-of f mono cont)
      tail-irrelevant = funext (⊑-antisymm left⊑right right⊑left)
```

Now, we can also move on to consider the denotational semantics.

```agda

  ℕ⟦_⟧ : WHILE-ℕ → 𝔻-ℕ
  ℕ⟦ ~ n ⟧ s = n
  ℕ⟦ N ++ M ⟧ s = ℕ⟦ N ⟧ s + ℕ⟦ M ⟧ s
  ℕ⟦ N ×× M ⟧ s = ℕ⟦ N ⟧ s * ℕ⟦ M ⟧ s
  ℕ⟦ v var ⟧ s = s var

  _≥_ : ℕ → ℕ → Bool
  zero ≥ zero = true
  zero ≥ suc m = false
  suc n ≥ zero = true
  suc n ≥ suc m = n ≥ m

  𝔹⟦_⟧ : WHILE-𝔹 → 𝔻-𝔹
  𝔹⟦ tt ⟧ s = true
  𝔹⟦ ff ⟧ s = false
  𝔹⟦ M ≫ N ⟧ s = ℕ⟦ M ⟧ s ≥ ℕ⟦ N ⟧ s 
  𝔹⟦ M ∧ N ⟧ s = 𝔹⟦ M ⟧ s && 𝔹⟦ N ⟧ s

  Command⟦_⟧ : WHILE-Command → 𝔻-Command
  Command⟦ var ≔ M ⟧ s = inl {!!} -- need decidability of 𝕍
  Command⟦ If B Then C₁ Else C₂ ⟧ s = if 𝔹⟦ B ⟧ s then Command⟦ C₁ ⟧ s
                                                  else Command⟦ C₂ ⟧ s
  Command⟦ While B Do C ⟧ = ⨆ (chain-of f mono cont)
    where
      f : 𝔻-Command → 𝔻-Command
      f w s = if 𝔹⟦ B ⟧ s then (Command⟦ C ⟧ >>> w) s else inl s 

      -- to show monotonic, we have to pattern match on (𝔹⟦ B ⟧ x).
      --   If it is false, then we take the else branch so f w₁ = f w₂.
      --   If it is true, then we have to further consider Command⟦ C ⟧ s
      --     If it is defined as some z, then since w₁ ⊑ w₂, they must agree on
      --       their action on z.
      --     If it is not defined, then the action of w₁ and w₂ are also undefined.
      mono : Monotonic f
      mono {w₁} {w₂} w₁⊑w₂ s hfw₁ with (𝔹⟦ B ⟧ s)
      ...                                  | false = refl _
      ...                                  | true with Command⟦ C ⟧ s
      ...                                            | inl z = w₁⊑w₂ z hfw₁
      ...                                            | inr ⋆ = refl _


      cont : Continuous f mono
      cont = {!!} -- depends on definition of lub

  Command⟦ C₁ ∘ C₂ ⟧ s = ((Command⟦ C₁ ⟧) >>> Command⟦ C₂ ⟧) s
  Command⟦ Skip ⟧ s = inl s
  
```
