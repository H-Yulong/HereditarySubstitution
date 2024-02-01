module Spine where

open import Syntax public

{- Syntax of normal and neutral in terms of spine -}

mutual
  data SNf : Con → Ty → Set where
    lam : ∀{Γ α β} → SNf (Γ , α) β → SNf Γ (α ⇒ β)
    neu : ∀{Γ} → SNe Γ ι → SNf Γ ι
  
  data SNe : Con → Ty → Set where
    _,_ : ∀{Γ α β} → Var Γ α → Sp Γ α β → SNe Γ β
  data Sp : Con → Ty → Ty → Set where
    ∙ : ∀{Γ α} → Sp Γ α α
    _,_ : ∀{Γ α β γ} → SNf Γ α → Sp Γ β γ → Sp Γ (α ⇒ β) γ

{- Renaming, weakening, and append -}
mutual
  renSNf : ∀{Γ Δ α} → SNf Γ α → Ren Γ Δ → SNf Δ α
  renSNf (lam t) ρ = lam (renSNf t (ext ρ))
  renSNf (neu (x , sp)) ρ = neu ((ρ x) , renSp sp ρ)

  renSp : ∀{Γ Δ α β} → Sp Γ α β → Ren Γ Δ → Sp Δ α β
  renSp ∙ ρ = ∙
  renSp (t , sp) ρ = renSNf t ρ , renSp sp ρ

renSNe : ∀{Γ Δ α} → SNe Γ α → Ren Γ Δ → SNe Δ α
renSNe (x , sp) ρ = ρ x , renSp sp ρ

wkSNf : ∀{Γ α β} → SNf Γ β → SNf (Γ , α) β
wkSNf t = renSNf t vs

wkSp : ∀{Γ α β γ} → Sp Γ β γ → Sp (Γ , α) β γ
wkSp sp = renSp sp vs

appSp : ∀{Γ α β γ} → Sp Γ γ (α ⇒ β) → SNf Γ α → Sp Γ γ β
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

++-comm : ∀{Γ α β γ τ} → (sp1 : Sp Γ α β)(sp2 : Sp Γ β γ)(sp3 : Sp Γ γ τ) →
  (sp1 ++ sp2) ++ sp3 ≡ sp1 ++ (sp2 ++ sp3)
++-comm ∙ sp2 sp3 = refl
++-comm (s , sp1) sp2 sp3 rewrite ++-comm sp1 sp2 sp3 = refl

appSp-++ : ∀{Γ α β γ ω}(sp : Sp Γ α (β ⇒ γ))(s' : SNf Γ β)(sp' : Sp Γ γ ω) → 
  appSp sp s' ++ sp' ≡ sp ++ (s' , sp')
appSp-++ ∙ s' sp' = refl
appSp-++ (s , sp) s' sp' = cong (λ z → s , z) (appSp-++ _ _ _)

_$$sp_ : ∀{Γ α β} → SNe Γ α → Sp Γ α β → SNe Γ β
(x , sp) $$sp sp' = x , sp ++ sp'

$$sp-z : ∀{Γ α} → (u : SNe Γ α) → u $$sp ∙ ≡ u
$$sp-z (x , sp) rewrite ++-z {sp = sp} = refl

$$sp-comm : ∀{Γ α β γ} → (u : SNe Γ α)(sp : Sp Γ α β)(sp' : Sp Γ β γ) 
  → (u $$sp sp) $$sp sp' ≡ u $$sp (sp ++ sp')
$$sp-comm (x , xs) sp sp' rewrite ++-comm xs sp sp' = refl

-------------------------------------


{- Eta expansion -}
mutual
  nvar : ∀{Γ σ} → Var Γ σ → SNf Γ σ
  nvar x = ne2nf (x , ∙)

  ne2nf : ∀{Γ σ} → SNe Γ σ → SNf Γ σ
  ne2nf {σ = ι} xns = neu xns
  ne2nf {σ = σ ⇒ τ} (x , ns) = lam (ne2nf (vs x , appSp (wkSp ns) (nvar vz)))

-------------------------------------

{- Hereditary substitution -}
mutual
  _[_,_] : ∀{Γ Δ α β} → SNf Γ α → Ren Γ (Δ , β) → SNf Δ β → SNf Δ α
  lam t [ ρ , u ] = lam (t [ sw ∘ ext ρ , wkSNf u ])
  neu (x , sp) [ ρ , u ] with ρ x
  ... | vz = u $ (sp < ρ , u >)
  ... | vs x = neu (x , (sp < ρ , u >))

  _<_,_> : ∀{Γ Δ α β γ} → Sp Γ α γ → Ren Γ (Δ , β) → SNf Δ β → Sp Δ α γ
  ∙ < ρ , u > = ∙
  (t , sp) < ρ , u > = (t [ ρ , u ]) , (sp < ρ , u >)

  _$_ : ∀{Γ α β} → SNf Γ α → Sp Γ α β → SNf Γ β
  t $ ∙ = t
  t $ (u , sp) = (napp t u) $ sp
  
  napp : ∀{Γ α β} → SNf Γ (α ⇒ β) → SNf Γ α → SNf Γ β
  napp (lam t) u = t [ id , u ]

-------------------------------------

{- Normalization -}
snf : ∀{Γ σ} → Tm Γ σ → SNf Γ σ
snf (var x) = nvar x
snf (lam t) = lam (snf t)
snf (app t u) = napp (snf t) (snf u)

-------------------------------------

{- Example terms -} 
t1 : Tm ∙ (ι ⇒ ι)
t1 = lam (var vz)

t2 : Tm (∙ , (ι ⇒ ι) ⇒ ι ⇒ ι) ((ι ⇒ ι) ⇒ ι ⇒ ι)
t2 = var vz

t3 : Tm (∙ , ι ⇒ ι , (ι ⇒ ι) ⇒ ι ⇒ ι) (ι ⇒ ι)
t3 = app (var vz) (var (vs vz))  

-- (f , g) ⊢ (λh. g h) f 
t4 : Tm (∙ , ι ⇒ ι , (ι ⇒ ι) ⇒ ι ⇒ ι) (ι ⇒ ι)
t4 = app (lam (app (var (vs vz)) (var vz))) (var (vs vz))

n1 : ∀{α β} → SNf (∙ , α , β) (ι ⇒ ι)
n1 = renSNf (lam (neu (vz , ∙))) (ext vs)
 
 