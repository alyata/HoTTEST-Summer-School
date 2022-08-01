```agda
{-# OPTIONS --without-K #-}

module hott-lecture-6 where

open import prelude
open import sums-equality

const : {A : Type} → A → A → A
const a x = a

module _ {A : Type} {B : A → Type} where
  -- homotopy laws
  ∼-refl : (f : (x : A) → B x) → f ∼ f
  ∼-refl f x = refl (f x)
                     
  ∼-inv : (f g : (x : A) → B x) → (f ∼ g) → (g ∼ f)
  ∼-inv f g H x = sym (H x)

  ∼-concat : (f g h : (x : A) → B x) → f ∼ g → g ∼ h → f ∼ h
  ∼-concat f g h H K x = trans (H x) (K x)


∼-assoc : {A B C D : Type} {f : C → D} {g : B → C} {h : A → B}
        → (f ∘ g) ∘ h ∼ f ∘ (g ∘ h)
∼-assoc x = refl _

-- whiskering

_<●_ : {A B C : Type} {f g : A → B} (h : B → C) (H : f ∼ g) → h ∘ f ∼ h ∘ g
h <● H = λ x → ap h (H x)

_●>_ : {A B C : Type} {f g : A → B} (H : f ∼ g) (h : C → A) → f ∘ h ∼ g ∘ h
H ●> h = λ x → H (h x)

-- equivalences
section : {A B : Type} (f : A → B) → Type
section {A} {B} f = Σ g ꞉ (B → A) , f ∘ g ∼ id

retr : {A B : Type} (f : A → B) → Type
retr {A} {B} f = Σ h ꞉ (B → A) , h ∘ f ∼ id


is-equiv : {A B : Type} (f : A → B) → Type
is-equiv f = section f × retr f

_≃_ : Type → Type → Type
A ≃ B = Σ f ꞉ (A → B) , is-equiv f

has-inverse : {A B : Type} (f : A → B) → Type
has-inverse {A} {B} f =  Σ g ꞉ (B → A) , ((f ∘ g ∼ id) × (g ∘ f ∼ id))

is-equiv-of-has-inverse :  {A B : Type} {f : A → B} → has-inverse f → is-equiv f
is-equiv-of-has-inverse (g , sect , retr) = (g , sect) , (g , retr)

has-inverse-of-is-equiv : {A B : Type} {f : A → B} → is-equiv f → has-inverse f
has-inverse-of-is-equiv {_} {_} {f} ((g , sect) , (h , ret)) = g , sect , gf∼id 
  where
    right : h ∘ (f ∘ g) ∼ h
    right = h <● sect

    left : g ∼ h ∘ (f ∘ g)
    left = ∼-concat _ _ _ (∼-inv _ _ (ret ●> g)) λ x → refl _

    g∼h : g ∼ h
    g∼h = ∼-concat _ _ _ left right

    gf∼id : g ∘ f ∼ id
    gf∼id = ∼-concat _ _ _ (g∼h ●> f) (ret)

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

equiv-of-contr : {A : Type} → is-contr A → is-equiv (λ (_ : A) → ⋆)
equiv-of-contr (c , C) = is-equiv-of-has-inverse ((λ _ → c) , sect , ret)
  where
    sect : ((λ _ → ⋆) ∘ (λ _ → c)) ∼ id
    sect ⋆ = refl ⋆

    ret : ((λ _ → c) ∘ (λ _ → ⋆)) ∼ id
    ret x = C x

contr-of-equiv : {A : Type} → is-equiv (λ (_ : A) → ⋆) → is-contr A
contr-of-equiv equiv with has-inverse-of-is-equiv equiv
...                       | g , sect , ret = g ⋆ , ret

-- Since contractible types are equivalent to 𝟙, they have all of the structural properties of 𝟙. We can generalise the induction on 𝟙 to singleton induction on contractible types.

-- singleton induction is expressed as the section of eval,
-- i.e. ind-sing a : B a → (x : A) → B x. Compare this with
-- 𝟙-induction.

singleton-induction : (A : Type) → (a : A) → Type₁
singleton-induction A a = (B : A → Type) → section (eval B)
  where
    eval : (B : A → Type) → ((x : A) → B x) → B a
    eval B all = all a

singleton-induction-of-is-contr : {A : Type} → ((a , C) : is-contr A) → singleton-induction A a
singleton-induction-of-is-contr {A} (a , C) B = ind-sing ,
  λ Ba → transport (λ q → transport B q Ba ≡ Ba)
                   (hC' a a (C a))
                   (refl _)
  where
    C' : (x : A) → a ≡ x
    C' x = (C a)⁻¹ ∙ (C x)

    -- In order to show the that ind-sing is the section,
    -- we need to rely on the fact that C' a ≡ refl
    -- Because Martin's library doesn't seem to include
    -- this useful lemma, we reprove it.
    hC' : (x y : A) → (p : x ≡ y) → refl y ≡ p ⁻¹ ∙ p
    hC' x .x (refl .x) = refl _
    
    ind-sing : B a → (x : A) → B x
    ind-sing Ba x = transport B (C' x) Ba

-- TODO: is-contr-of-singleton-induction

-- The goal is to prove that a contractible type also has
-- contractible identities:
-- {A : Type} → is-contr A → (x y : A) → is-contr (x ≡ y)

-- first we prove the special case for 𝟙 to get a feel for the
-- problem. We can do this by proving the equivalence of the - -- identities of 𝟙 with 𝟙 itself.

exercise-3' : (x y : 𝟙) → is-equiv (λ (p : x ≡ y) → ⋆)
exercise-3' ⋆ ⋆ = is-equiv-of-has-inverse ((λ _ → refl ⋆) , sect , ret)
  where
    sect : ((λ _ → ⋆) ∘ (λ _ → refl ⋆)) ∼ id
    sect ⋆ = refl _

    ret : ((λ _ → refl ⋆) ∘ (λ _ → ⋆)) ∼ id
    ret (refl .⋆) = refl _

-- The necessary induction principles here are 𝟙-induction and
-- ≡-induction. For the general case, we simply need to replace -- the top level 𝟙-inductions with singleton induction.

exercise-3 : {A : Type} → is-contr A
           → (x y : A) → is-contr (x ≡ y)
exercise-3 {A} (c , C) x y = contr-of-equiv (exercise-3'' x y)
  where
    singleton-induction-c : singleton-induction A c
    singleton-induction-c =
      singleton-induction-of-is-contr (c , C)

    ind : {B : A → Type} → B c → (x : A) → B x
    ind {B} = pr₁ (singleton-induction-c B)

    ind-comp : {B : A → Type} → (Bc : B c) → ind {B} Bc c ≡ Bc
    ind-comp {B} = pr₂ (singleton-induction-c B)

    exercise-3'' : (x y : A) → is-equiv (λ (p : x ≡ y) → ⋆)
    exercise-3'' x y = is-equiv-of-has-inverse (inv , sect , ret)
      where

        inv : 𝟙 → x ≡ y
        inv _ = ind {λ x → x ≡ y}
                    (ind {λ y → c ≡ y} (refl c) y)
                    x
    
        sect : ((λ _ → ⋆) ∘ inv) ∼ id
        sect ⋆ = refl _

        -- This would be a lot less painful if ind-comp were
        -- definitional
        ret : (inv ∘ (λ _ → ⋆)) ∼ id
        ret (refl .x) =
         transport
          (λ z → ind {λ x → x ≡ z}
                     (ind {λ y → c ≡ y} (refl c) z)
                     z
                 ≡ refl z)
          (C x)
          (ind-comp (ind {λ y → c ≡ y} (refl c) c)
           ∙ ind-comp (refl c))

exercise-5 : {A B : Type} → (f : A → B) → A ≃ (Σ y ꞉ B , Σ x ꞉ A , f x ≡ y)
exercise-5 {A} {B} f = l-to-r , (r-to-l , sect) , r-to-l , ret
  where
    l-to-r : A → (Σ y ꞉ B , Σ x ꞉ A , f x ≡ y)
    l-to-r a = f a , a , refl (f a)

    r-to-l : (Σ y ꞉ B , Σ x ꞉ A , f x ≡ y) → A
    r-to-l (y , x , p) = x

    sect : (l-to-r ∘ r-to-l) ∼ id
    sect (.(f x) , x , refl .(f x)) =
      to-Σ-≡ (refl (f x) ,
              (to-Σ-≡ (refl x , refl (refl (f x)))))

    ret : (r-to-l ∘ l-to-r) ∼ id
    ret x = refl _
```
