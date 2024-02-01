module Stack where

open import Syntax public

{- Stacks -}
data St : Con → Ty → Ty → Set where
  ∙ : ∀{Γ α} → St Γ α α
  _,_ : ∀{Γ α β γ} → Nf Γ α → St Γ β γ → St Γ (α ⇒ β) γ

renSt : ∀{Γ Δ α β} → St Γ α β → Ren Γ Δ → St Δ α β
renSt ∙ ρ = ∙
renSt (t , st) ρ = renNf t ρ , renSt st ρ

wkSt : ∀{Γ α β γ} → St Γ β γ → St (Γ , α) β γ
wkSt st = renSt st vs

{- Fold with app -}
_$$_ : ∀{Γ α β} → Ne Γ α → St Γ α β → Ne Γ β
t $$ ∙ = t
t $$ (u , st) = app t u $$ st

{- Joining two stacks -}

appSt : ∀{Γ α β γ} → St Γ α (β ⇒ γ) → Nf Γ β → St Γ α γ 
appSt ∙ t = t , ∙
appSt (s , st) t = s , appSt st t

infix 10 _++_
_++_ : ∀{Γ α β γ} → St Γ α β → St Γ β γ → St Γ α γ
∙ ++ st' = st'
(x , st) ++ st' = x , st ++ st'

++-z : ∀{Γ α β}{st : St Γ α β} → st ++ ∙ ≡ st
++-z {st = ∙} = refl
++-z {st = x , st} rewrite ++-z {st = st} = refl

$$-++ : ∀{Γ α β γ}(t : Ne Γ α)(st : St Γ α β)(st' : St Γ β γ) → 
  t $$ (st ++ st') ≡ (t $$ st) $$ st'
$$-++ t ∙ st' = refl
$$-++ t (u , st) st' rewrite $$-++ (app t u) st st' = refl

-- $$-++ : ∀{Γ α β γ ω}(st : St Γ α (β ⇒ γ))(s' : Ne Γ β)(st' : St Γ γ ω) → 
--   (st $$ s') ++ st' ≡ st ++ (s' , st')
-- $$-++ ∙ s' st' = refl
-- $$-++ (s , st) s' st' = cong (λ z → s , z) ($$-++ _ _ _)

-------------------------------------

{- Eta expansion -}

mutual
  ne2nf : ∀{Γ σ} → Ne Γ σ → Nf Γ σ
  ne2nf {σ = ι} t = ↓ t
  ne2nf {σ = α ⇒ β} t = lam ( ne2nf (app (wkNe t) (ηvar vz)) )
   
  ηvar : ∀{Γ σ} → Var Γ σ → Nf Γ σ
  ηvar x = ne2nf (var x)

-------------------------------------

{- Hereditary substitutions -}

mutual
  _[_,_] : ∀{Γ Δ α β} → Nf Γ α → Ren Γ (Δ , β) → Nf Δ β → Nf Δ α
  lam t [ ρ , u ] = lam ( t [ sw ∘ ext ρ , wkNf u ] )
  ↓ t [ ρ , u ] = t < ρ , u > ∙

  _<_,_>_ : ∀{Γ Δ α β} →
    Ne Γ α → Ren Γ (Δ , β) → Nf Δ β → St Δ α ι → Nf Δ ι
  var x < ρ , u > sp with ρ x
  ... | vz = u $ sp
  ... | vs x = ne2nf (var x $$ sp)
  app t1 t2 < ρ , u > sp = t1 < ρ , u > ( t2 [ ρ , u ] , sp )

  -- fold with napp
  _$_ : ∀{Γ α β} → Nf Γ α → St Γ α β → Nf Γ β
  t $ ∙ = t
  t $ ( u , st ) = (napp t u) $ st
  
  napp : ∀{Γ α β} → Nf Γ (α ⇒ β) → Nf Γ α → Nf Γ β
  napp (lam t) u = t [ id , u ]

-------------------------------------

{- Normalization -}

nf : ∀{Γ σ} → Tm Γ σ → Nf Γ σ
nf (var x) = ηvar x
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

-- (f , g) ⊢ (λh. g h) f 
t4 : Tm (∙ , ι ⇒ ι , (ι ⇒ ι) ⇒ ι ⇒ ι) (ι ⇒ ι)
t4 = app (lam (app (var (vs vz)) (var vz))) (var (vs vz))

n1 : ∀{α β} → Nf (∙ , α , β) (ι ⇒ ι)
n1 = renNf (lam (↓ (var vz))) (ext vs)

-------------------------------------

_[_,_]St : ∀{Γ Δ α β γ} → St Γ α γ → Ren Γ (Δ , β) → Nf Δ β → St Δ α γ
∙ [ ρ , t ]St = ∙
(s , st) [ ρ , t ]St = s [ ρ , t ] , st [ ρ , t ]St

$$-<> : ∀{Γ Δ α β γ}(u : Ne Γ α)(st : St Γ α γ)(ρ : Ren Γ (Δ , β))(t : Nf Δ β)(st' : St Δ γ ι) → 
  (u $$ st) < ρ , t > st' ≡ u < ρ , t > ((st [ ρ , t ]St) ++ st')
$$-<> u ∙ ρ t st' = refl
$$-<> u (s , st) ρ t st' rewrite $$-<> (app u s) st ρ t st' = refl

<>Ne-vz : ∀{Γ Δ α}{x : Var Γ α}{st : St Δ α ι}{u : Nf Δ α}{ρ : Ren Γ (Δ , α)} → 
  ρ x ≡ vz → (u $ st) ≡ (var x) < ρ , u > st
<>Ne-vz p rewrite p = refl

<>Ne-vs : ∀{Γ Δ α β}{x : Var Γ α}{y : Var Δ α}{st : St Δ α ι}{u : Nf Δ β}{ρ : Ren Γ (Δ , β)} → 
  ρ x ≡ (vs y) → ne2nf (var y $$ st) ≡ (var x) < ρ , u > st
<>Ne-vs p rewrite p = refl

