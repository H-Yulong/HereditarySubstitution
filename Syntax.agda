module Syntax where

open import Basic public

infixl 5 _,_
infixr 10 _⇒_

{- Syntax -}
data Ty : Set where 
  ι : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙ : Con
  _,_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀{Γ α} → Var (Γ , α) α
  vs : ∀{Γ α β} → Var Γ α → Var (Γ , β) α

data Tm : Con → Ty → Set where
  var : ∀{Γ α} → Var Γ α → Tm Γ α
  lam : ∀{Γ α β} → Tm (Γ , α) β → Tm Γ (α ⇒ β)
  app : ∀{Γ α β} → Tm Γ (α ⇒ β) → Tm Γ α → Tm Γ β

-------------------------------------

{- Renamings: identity, extension, swap -}
Ren : Con → Con → Set
Ren Γ Δ = ∀{α} → Var Γ α → Var Δ α

id : ∀{Γ} → Ren Γ Γ
id x = x

ext : ∀{Γ Δ α} → Ren Γ Δ → Ren (Γ , α) (Δ , α)
ext ρ vz = vz
ext ρ (vs x) = vs (ρ x)

sw : ∀{Γ β1 β2} → Ren (Γ , β1 , β2) (Γ , β2 , β1)
sw vz = vs vz
sw (vs vz) = vz
sw (vs (vs x)) = vs (vs x)

{- Renaming on terms -}
ren : ∀{Γ Δ α} → Tm Γ α → Ren Γ Δ → Tm Δ α
ren (var x) ρ = var (ρ x)
ren (lam t) ρ = lam (ren t (ext ρ))
ren (app s t) ρ = app (ren s ρ) (ren t ρ)

wk : ∀{Γ α β} → Tm Γ α → Tm (Γ , β) α
wk t = ren t vs

-------------------------------------

{- Recursive, CPS-ed single variable substitution.
   s [ ρ , t ]Tm means: 
    perform renaming ρ on s, then 
    substitute de Bruijn index 0 with t. -}

_[_,_]Tm : ∀{Γ Δ α β} → Tm Γ α → Ren Γ (Δ , β) → Tm Δ β → Tm Δ α
var x [ ρ , t ]Tm with ρ x
... | vz = t
... | vs y = var y
lam s [ ρ , t ]Tm = lam (s [ sw ∘ ext ρ , ren t vs ]Tm)
app s s' [ ρ , t ]Tm = app (s [ ρ , t ]Tm) (s' [ ρ , t ]Tm)

_[_]0 : ∀{Γ α β} → Tm (Γ , β) α → Tm Γ β → Tm Γ α
t [ u ]0 = t [ id , u ]Tm

-------------------------------------

{- Neutral and Normal -}
mutual
  data Nf : Con → Ty → Set where
    lam : ∀{Γ α β} → Nf (Γ , α) β → Nf Γ (α ⇒ β)
    ↓ : ∀{Γ} → Ne Γ ι → Nf Γ ι
  
  data Ne : Con → Ty → Set where
    var : ∀{Γ α} → Var Γ α → Ne Γ α
    app : ∀{Γ α β} → Ne Γ (α ⇒ β) → Nf Γ α → Ne Γ β

{- Renaming, weakening, and append -}
mutual
  renNf : ∀{Γ Δ α} → Nf Γ α → Ren Γ Δ → Nf Δ α
  renNf (↓ t) ρ = ↓ (renNe t ρ)
  renNf (lam t) ρ = lam (renNf t (ext ρ))

  renNe : ∀{Γ Δ α} → Ne Γ α → Ren Γ Δ → Ne Δ α
  renNe (var x) ρ = var (ρ x)
  renNe (app t1 t2) ρ = app (renNe t1 ρ) (renNf t2 ρ)

wkNf : ∀{Γ α β} → Nf Γ β → Nf (Γ , α) β
wkNf t = renNf t vs

wkNe : ∀{Γ α β} → Ne Γ β → Ne (Γ , α) β
wkNe t = renNe t vs


{- βη-equality -}
infixr 20 _=>_
infixl 20 _-$-_
data _≡t_ : ∀{Γ α} → Tm Γ α → Tm Γ α → Set where
  ≡β : ∀{Γ α β}{t : Tm (Γ , α) β}{u : Tm Γ α} → app (lam t) u ≡t (t [ u ]0)
  ≡η : ∀{Γ α β}{t : Tm Γ (α ⇒ β)} → t ≡t lam (app (wk t) (var vz)) 
  -- inverses
  ≡β⁻¹ : ∀{Γ α β}{t : Tm (Γ , α) β}{u : Tm Γ α} → (t [ u ]0) ≡t app (lam t) u
  ≡η⁻¹ : ∀{Γ α β}{t : Tm Γ (α ⇒ β)} → lam (app (wk t) (var vz)) ≡t t
  -- reflexive, transitivity
  idᵗ : ∀{Γ α}{t : Tm Γ α} → t ≡t t
  _=>_ : ∀{Γ α}{t u v : Tm Γ α} → t ≡t u → u ≡t v → t ≡t v
  -- congruence under lam and app
  λt : ∀{Γ α β}{t u : Tm (Γ , α) β} → t ≡t u → lam t ≡t lam u
  _-$-_ : ∀{Γ α β}{t t' : Tm Γ (α ⇒ β)}{u u' : Tm Γ α} → 
      t ≡t t' → u ≡t u' → app t u ≡t app t' u'


