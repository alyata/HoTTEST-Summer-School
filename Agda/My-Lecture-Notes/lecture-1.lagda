Lecture 1 of HoTT in Agda, 6 July 2022, by Martin Escardo

\begin{code}
{-# OPTIONS --without-K --safe #-}

module lecture-1 where

open import general-notation
\end{code}

To begin with, we define the type of booleans by listing its two inhabitants,
`true` and false.

\begin{code}
data Bool : Type where
  true false : Bool
\end{code}

We can define functions using booleans:

\begin{code}
not : Bool → Bool
not true = false
not false = true

idBool : Bool → Bool
idBool x = x

idBool' : Bool → Bool
idBool' = λ (x : Bool) → x
\end{code}

We can define the identity function on an arbitrary type

\begin{code}
id : (A : Type) → A → A
id A x = x

-- We can use underscore _ to let agda figure out a certain argument
idBool'' : Bool → Bool
idBool'' = id _
\end{code}

In most scenarios, A can be automatically inferred, so we can have Agda infer it for us by making tha rgument implicit. Even better way to allow it to be automatically inferred:

\begin{code}
id' : {A : Type} → A → A
id' x = x

idBool''' : Bool → Bool
idBool''' = id'

-- To pass in implicit arguments manually:
idBool'''' : Bool → Bool
idBool'''' = id' {Bool}
\end{code}

We can have functions that return functions, but using lambda notation can get cumbersome so we can instead define a local function using `where`.

\begin{code}

-- Recall "Propositions as types" from HoTT lecture 1.
example : {P Q : Type} → P → (Q → P)
example {P} {Q} p = f
  where
    f : Q → P
    f _ = p

-- underscore on lefthand side means instantiate argument but we're not gonna use it so don't give it a name.
\end{code}

To use product type/conjunction, do

\begin{code}
open import binary-products

ex : {P Q : Type} → P × Q → Q × P 
ex (p , q) = q , p
\end{code}

Now let's move on to natural numbers:

\begin{code}

-- ℕ is written as `\bN`
data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

three : ℕ
three = succ (succ (succ ( zero ) ) )

-- Use numerical notation for ℕ
{-# BUILTIN NATURAL ℕ #-}

three' : ℕ
three' = 3

-- Dependent types
D : Bool → Type
D true = ℕ
D false = Bool

if_then_else_ : {X : Type} → Bool → X → X → X
if true then x else y = x
if false then x else y = y

--dependent if-then-else - the then and else can be different types...

if[_]_then_else_ : (X : Bool → Type) →
                   (b : Bool) → X true → X false → X b
if[ X ] true then x else y = x
if[ X ] false then x else y = y

\end{code}

Now, we define the type of lists. Rather List is a function from Type to Type

\begin{code}
data List (A : Type) : Type where
  []   : List A
  _::_ : A → List A → List A

ff : Type → Type
ff = List

sample-list₀ : List ℕ
sample-list₀ = 0 :: (1 :: (2 :: []))

-- Brackets annoying, so we say :: is right associative with a precedence
infixr 10 _::_

length : {X : Type} → List X → ℕ
length [] = 0
length (x :: xs) = succ $ (length xs)

\end{code}


