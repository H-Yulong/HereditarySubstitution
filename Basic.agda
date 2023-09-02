module Basic where

open import Agda.Primitive public
open import Agda.Builtin.Sigma renaming (_,_ to _Σ,_) public
open import Agda.Builtin.Bool public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans; cong₂) public

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

coerce : ∀{k l}{X : Set k}{s t : X} ->
  s ≡ t -> (P : X -> Set l) -> P s -> P t
coerce refl P p = p
