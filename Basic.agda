module Basic where

open import Agda.Primitive public
open import Agda.Builtin.Sigma renaming (_,_ to _Σ,_) public
open import Agda.Builtin.Bool public

-- open import Relation.Binary.PropositionalEquality

infixl 20 _×_ 
infixl 15 _+_
infixr 20 _∘_

_×_ : {m n : Level} → Set m → Set n → Set (m ⊔ n)
A × B = Σ A (λ _ → B)

_+_ : Set → Set → Set
A + B = Σ Bool (λ {true -> A; false -> B})

inl : ∀{A B} → A → A + B
inl a = (true Σ, a)

inr : ∀{A B} → B → A + B
inr b = (false Σ, b)

_∘_ : {A : Set} {B : A → Set} {C : {x : A} → B x → Set}
      (f : {x : A}(y : B x) → C y) (g : (x : A) → B x) (x : A) → C (g x)
(f ∘ g) x = f (g x)

-- Library of equality

infix 4 _≡_
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

cong : ∀{i}{A B : Set i} → (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : 
  ∀{i}{A B C : Set i} →
  (f : A → B → C) → {x y : A} → {u v : B} → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

sym : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

coerce : ∀{k l}{X : Set k}{s t : X} ->
  s ≡ t -> (P : X -> Set l) -> P s -> P t
coerce refl P p = p
