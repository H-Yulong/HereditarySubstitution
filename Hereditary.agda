module Hereditary where

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
  tt : ∀{Γ} → Tm Γ ι
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
ren tt ρ = tt
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
tt [ ρ , t ]Tm = tt
var x [ ρ , t ]Tm with ρ x
... | vz = t
... | vs y = var y
lam s [ ρ , t ]Tm = lam (s [ sw ∘ ext ρ , ren t vs ]Tm)
app s s' [ ρ , t ]Tm = app (s [ ρ , t ]Tm) (s' [ ρ , t ]Tm)

_[_]0 : ∀{Γ α β} → Tm (Γ , β) α → Tm Γ β → Tm Γ α
t [ u ]0 = t [ id , u ]Tm

-------------------------------------

{- Neutral, Normal, Spine -}
mutual
  data Nf : Con → Ty → Set where
    tt : ∀{Γ} → Nf Γ ι
    lam : ∀{Γ α β} → Nf (Γ , α) β → Nf Γ (α ⇒ β)
    neu : ∀{Γ} → Ne Γ ι → Nf Γ ι
  
  data Ne : Con → Ty → Set where
    _,_ : ∀{Γ α β} → Var Γ α → Sp Γ α β → Ne Γ β
  data Sp : Con → Ty → Ty → Set where
    ∙ : ∀{Γ α} → Sp Γ α α
    _,_ : ∀{Γ α β γ} → Nf Γ α → Sp Γ β γ → Sp Γ (α ⇒ β) γ

{- Renaming, weakening, and append -}
mutual
  renNf : ∀{Γ Δ α} → Nf Γ α → Ren Γ Δ → Nf Δ α
  renNf tt ρ = tt
  renNf (lam t) ρ = lam (renNf t (ext ρ))
  renNf (neu (x , sp)) ρ = neu ((ρ x) , renSp sp ρ)

  renSp : ∀{Γ Δ α β} → Sp Γ α β → Ren Γ Δ → Sp Δ α β
  renSp ∙ ρ = ∙
  renSp (t , sp) ρ = renNf t ρ , renSp sp ρ

renNe : ∀{Γ Δ α} → Ne Γ α → Ren Γ Δ → Ne Δ α
renNe (x , sp) ρ = ρ x , renSp sp ρ

wkNf : ∀{Γ α β} → Nf Γ β → Nf (Γ , α) β
wkNf t = renNf t vs

wkSp : ∀{Γ α β γ} → Sp Γ β γ → Sp (Γ , α) β γ
wkSp sp = renSp sp vs

appSp : ∀{Γ α β γ} → Sp Γ γ (α ⇒ β) → Nf Γ α → Sp Γ γ β
appSp ∙ t = t , ∙
appSp (f , sp) t = f , appSp sp t

{- Joining two spines -}
infix 10 _++_
_++_ : ∀{Γ α β γ} → Sp Γ α β → Sp Γ β γ → Sp Γ α γ
∙ ++ sp' = sp'
(x , sp) ++ sp' = x , sp ++ sp'

++-z : ∀{Γ α β}{sp : Sp Γ α β} → sp ++ ∙ ≡ sp
++-z {sp = ∙} = refl
++-z {sp = x , sp} rewrite ++-z {sp = sp} = refl

appSp-++ : ∀{Γ α β γ ω}(sp : Sp Γ α (β ⇒ γ))(s' : Nf Γ β)(sp' : Sp Γ γ ω) → 
  appSp sp s' ++ sp' ≡ sp ++ (s' , sp')
appSp-++ ∙ s' sp' = refl
appSp-++ (s , sp) s' sp' = cong (λ z → s , z) (appSp-++ _ _ _)

-------------------------------------

{- Eta expansion -}
mutual
  nvar : ∀{Γ σ} → Var Γ σ → Nf Γ σ
  nvar x = ne2nf (x , ∙)

  ne2nf : ∀{Γ σ} → Ne Γ σ → Nf Γ σ
  ne2nf {σ = ι} xns = neu xns
  ne2nf {σ = σ ⇒ τ} (x , ns) = lam (ne2nf (vs x , appSp (wkSp ns) (nvar vz)))

-------------------------------------

{- Hereditary substitution -}
mutual
  _[_,_] : ∀{Γ Δ α β} → Nf Γ α → Ren Γ (Δ , β) → Nf Δ β → Nf Δ α
  tt [ ρ , u ] = tt
  lam t [ ρ , u ] = lam (t [ sw ∘ ext ρ , wkNf u ])
  neu (x , sp) [ ρ , u ] with ρ x
  ... | vz = u $ (sp < ρ , u >)
  ... | vs x = neu (x , (sp < ρ , u >))

  _<_,_> : ∀{Γ Δ α β γ} → Sp Γ α γ → Ren Γ (Δ , β) → Nf Δ β → Sp Δ α γ
  ∙ < ρ , u > = ∙
  (t , sp) < ρ , u > = (t [ ρ , u ]) , (sp < ρ , u >)

  _$_ : ∀{Γ α β} → Nf Γ α → Sp Γ α β → Nf Γ β
  t $ ∙ = t
  t $ (u , sp) = (napp t u) $ sp
  
  napp : ∀{Γ α β} → Nf Γ (α ⇒ β) → Nf Γ α → Nf Γ β
  napp (lam t) u = t [ id , u ]

-------------------------------------

{- Normalization -}
nf : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
nf tt = tt
nf (var x) = nvar x
nf (lam t) = lam (nf t)
nf (app t u) = napp (nf t) (nf u)

-------------------------------------

{- Example terms -} 
t1 : Tm ∙ (ι ⇒ ι)
t1 = lam (var vz)

t2 : Tm (∙ , (ι ⇒ ι) ⇒ ι ⇒ ι) ((ι ⇒ ι) ⇒ ι ⇒ ι)
t2 = var vz

t3 : Tm (∙ , ι ⇒ ι , (ι ⇒ ι) ⇒ ι ⇒ ι) (ι ⇒ ι)
t3 = app (var vz) (var (vs vz))  

n1 : ∀{α β} → Nf (∙ , α , β) (ι ⇒ ι)
n1 = renNf (lam (neu (vz , ∙))) (ext vs)
