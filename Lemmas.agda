module Lemmas where

open import Spine

-------------------------------------

{- Renaming algebra -}

-- extension preserves extensional equality
ext-∀ : ∀{Γ Δ α β}{ρ σ : Ren Γ Δ}{x : Var (Γ , α) β} → 
  (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → ext ρ x ≡ ext σ x
ext-∀ {x = vz} p = refl
ext-∀ {x = vs x} p = cong vs p

-- the same for (sw ∘ ext _)
sw-ext-∀ : ∀{Γ Δ α β γ}{ρ σ : Ren Γ (Δ , β)}{x : Var (Γ , α) γ} → 
  (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → (sw ∘ ext ρ) x ≡ (sw ∘ ext σ) x
sw-ext-∀ {x = vz} p = refl
sw-ext-∀ {x = vs x} p = cong (sw ∘ vs) p

-- ext of id is still id
ext-id : ∀{Γ α β}{x : Var (Γ , α) β} → (ext id) x ≡ id x
ext-id {x = vz} = refl
ext-id {x = vs x} = refl

-- ext distributes over compose
ext-∘ : ∀{Γ Δ Ω α β}{ρ : Ren Γ Δ}{σ : Ren Δ Ω} → 
   {x : Var (Γ , α) β} → (ext (σ ∘ ρ)) x ≡ (ext σ ∘ ext ρ) x
ext-∘ {x = vz} = refl
ext-∘ {x = vs x} = refl

-- two equivalent ways to go from Γ to (Δ , β , α) using ρ : Γ → (Δ , α) and vs (new var's type β)
-- 1. apply ρ, then apply extended version of vs
-- 2. apply vs, then extended version of ρ, then swap
sw-ext : ∀{Γ Δ α β γ}{ρ : Ren Γ (Δ , α)} → 
  {x : Var Γ γ} → (ext (vs {β = β}) ∘ ρ) x ≡ (sw ∘ ext ρ ∘ vs) x
sw-ext {ρ = ρ} {x = x} with ρ x 
... | vz = refl
... | vs y = refl

-- swapping twice does nothing
sw-sw-id : ∀{Γ α β γ}{x : Var (Γ , α , β) γ} →
  (sw ∘ sw) x ≡ x
sw-sw-id {x = vz} = refl
sw-sw-id {x = vs vz} = refl
sw-sw-id {x = vs (vs x)} = refl

-- two equivalent ways to permute the first 3 vars
sw-3-perm : ∀{Γ α0 α1 α2 β} → {x : Var (Γ , α2 , α1 , α0) β} → 
  (sw ∘ ext sw ∘ sw) x ≡ (ext sw ∘ sw ∘ ext sw) x
sw-3-perm {x = vz} = refl
sw-3-perm {x = vs vz} = refl
sw-3-perm {x = vs (vs vz)} = refl
sw-3-perm {x = vs (vs (vs x))} = refl

-- sw commutes with 2-var ext
-- (since the extension does not affect the first two variables)
ext2-sw : ∀{Γ Δ α0 α1 β}{σ : Ren Γ Δ}{x : Var (Γ , α1 , α0) β} → 
  ((ext (ext σ)) ∘ sw) x ≡ (sw ∘ ext (ext σ)) x
ext2-sw {x = vz} = refl
ext2-sw {x = vs vz} = refl
ext2-sw {x = vs (vs x)} = refl

-------------------------------------

{- Renamings acting on terms -}

-- renaming congruence under Tm, SNf, Ne, and Sp
ren-cong : ∀{Γ Δ α}{ρ σ : Ren Γ Δ}{t : Tm Γ α} → 
  (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → ren t ρ ≡ ren t σ 
ren-cong {t = var x} p = cong var p
ren-cong {t = lam t} p = cong lam (ren-cong (ext-∀ p))
ren-cong {t = app s t} p = cong₂ app (ren-cong p) (ren-cong p)

mutual 
  renSNf-cong : ∀{Γ Δ α}{ρ σ : Ren Γ Δ}{t : SNf Γ α} → 
    (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → renSNf t ρ ≡ renSNf t σ 
  renSNf-cong {t = lam t} p = cong lam (renSNf-cong (ext-∀ p))
  renSNf-cong {t = neu (x , sp)} p = cong₂ (λ z z' → neu (z , z')) p (renSp-cong p)

  renSp-cong : ∀{Γ Δ α β}{ρ σ : Ren Γ Δ}{sp : Sp Γ α β} → 
    (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → renSp sp ρ ≡ renSp sp σ 
  renSp-cong {sp = ∙} p = refl
  renSp-cong {sp = t , sp} p = cong₂ _,_ (renSNf-cong p) (renSp-cong p)


-- composed renamings are the same as rename twice (for Tm, SNf, Ne, Sp)
ren-∘ : ∀{Γ Δ Ω α}{ρ : Ren Γ Δ}{σ : Ren Δ Ω} → 
  {t : Tm Γ α} → ren t (σ ∘ ρ) ≡ ren (ren t ρ) σ
ren-∘ {t = var x} = refl
ren-∘ {t = lam t} = cong lam (trans (ren-cong ext-∘) ren-∘)
ren-∘ {t = app s t} = cong₂ app ren-∘ ren-∘

mutual
  renSNf-∘ : ∀{Γ Δ Ω α}{ρ : Ren Γ Δ}{σ : Ren Δ Ω} → 
    {t : SNf Γ α} → renSNf t (σ ∘ ρ) ≡ renSNf (renSNf t ρ) σ
  renSNf-∘ {t = lam t} = cong lam (trans (renSNf-cong ext-∘) renSNf-∘)
  renSNf-∘ {t = neu (x , sp)} = cong₂ (λ z z' → neu (z , z')) refl renSp-∘

  renSp-∘ : ∀{Γ Δ Ω α β}{ρ : Ren Γ Δ}{σ : Ren Δ Ω} → 
    {sp : Sp Γ α β} → renSp sp (σ ∘ ρ) ≡ renSp (renSp sp ρ) σ
  renSp-∘ {sp = ∙} = refl
  renSp-∘ {sp = t , sp} = cong₂ _,_ renSNf-∘ renSp-∘


-- identity renaming does nothing
mutual
  renSNf-id : ∀{Γ α}{u : SNf Γ α} → renSNf u id ≡ u
  renSNf-id {u = lam u} = cong lam (trans (renSNf-cong ext-id) renSNf-id)
  renSNf-id {u = neu (x , sp)} rewrite renSp-id {sp = sp} = refl

  renSp-id : ∀{Γ α β}{sp : Sp Γ α β} → renSp sp id ≡ sp
  renSp-id {sp = ∙} = refl
  renSp-id {sp = x , sp} = cong₂ _,_ renSNf-id renSp-id

-------------------------------------

{- Interaction between renaming and auxiliary functions -}

-- appSp respects reaming
appSp-ren : ∀{Γ Δ α β γ} → (sp : Sp Γ α (β ⇒ γ)) → (t : SNf Γ β) → (ρ : Ren Γ Δ) → 
  renSp (appSp sp t) ρ ≡ appSp (renSp sp ρ) (renSNf t ρ)
appSp-ren ∙ t ρ = refl
appSp-ren (u , sp) t ρ rewrite appSp-ren sp t ρ = refl

renNe-lem : ∀{Γ Δ} → (t : SNe Γ ι) → (ρ : Ren Γ Δ) → 
  renSNf (neu t) ρ ≡ neu (renSNe t ρ)
renNe-lem (x , sp) ρ = refl

-- η-expansion respects renaming
mutual
  nvar-ren : ∀{Γ Δ α} → (x : Var Γ α) → (ρ : Ren Γ Δ) → 
    renSNf (nvar x) ρ ≡ nvar (ρ x)
  nvar-ren x ρ = ne2nf-ren (x , ∙) ρ

  ne2nf-ren : ∀{Γ Δ α} → (t : SNe Γ α) → (ρ : Ren Γ Δ) → 
    renSNf (ne2nf t) ρ ≡ ne2nf (renSNe t ρ)
  ne2nf-ren {α = ι} t ρ = renNe-lem t ρ
  ne2nf-ren {α = α ⇒ β} (x , sp) ρ = 
    cong lam
    (trans (ne2nf-ren (vs x , appSp (renSp sp vs) (ne2nf (vz , ∙))) (ext ρ)) 
    (cong (λ z → ne2nf (vs (ρ x) , z)) 
    (trans (appSp-ren (renSp sp vs) (ne2nf (vz , ∙)) (ext ρ)) 
    (cong₂ appSp (trans (sym renSp-∘) renSp-∘) (nvar-ren vz (ext ρ))))))

-------------------------------------

{- Substitutions on terms -}
-- all substitutions here are single-varible

-- substitutions on variables 
[]Tm-vz : ∀{Γ Δ β}{x : Var Γ β}{ρ : Ren Γ (Δ , β)}{t : Tm Δ β} → 
  ρ x ≡ vz → (var x) [ ρ , t ]Tm ≡ t
[]Tm-vz p rewrite p = refl

[]Tm-vs : ∀{Γ Δ α β}{x : Var Γ α}{y : Var Δ α}{ρ : Ren Γ (Δ , β)}{t : Tm Δ β} → 
  ρ x ≡ vs y → (var x) [ ρ , t ]Tm ≡ var y
[]Tm-vs p rewrite p = refl

neu[]-vz : ∀{Γ Δ α}{x : Var Γ α}{sp : Sp Γ α ι}{u : SNf Δ α}{ρ : Ren Γ (Δ , α)} → 
  ρ x ≡ vz → (u $ (sp < ρ , u >)) ≡ (neu (x , sp)) [ ρ , u ]
neu[]-vz p rewrite p = refl

neu[]-vs : ∀{Γ Δ α β}{x : Var Γ α}{sp : Sp Γ α ι}{y : Var Δ α}{u : SNf Δ β}{ρ : Ren Γ (Δ , β)} → 
  ρ x ≡ (vs y) → neu (y , (sp < ρ , u >)) ≡ (neu (x , sp)) [ ρ , u ]
neu[]-vs p rewrite p = refl

-------------------------------------

{- Six key lemmas -}
-- used in soundness proofs

-- 1. The congruence rule
mutual
  []-ren-cong : ∀{Γ Δ α β}{t : SNf Γ α}{u : SNf Δ β}{ρ σ : Ren Γ (Δ , β)} → 
    (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → t [ ρ , u ] ≡ t [ σ , u ]
  []-ren-cong {t = lam t} p = cong lam ([]-ren-cong {t = t} (sw-ext-∀ p))
  []-ren-cong {t = neu (x , sp)} {u = u} {ρ = ρ} p with ρ x in eq
  ... | vz = trans (cong₂ _$_ refl (<>-ren-cong {sp = sp} p)) (neu[]-vz {sp = sp} (trans (sym p) eq))
  ... | vs y = trans (cong neu (cong₂ _,_ refl (<>-ren-cong p))) (neu[]-vs (trans (sym p) eq))

  <>-ren-cong : ∀{Γ Δ α β γ}{sp : Sp Γ α γ}{u : SNf Δ β}{ρ σ : Ren Γ (Δ , β)} → 
    (∀{β}{x : Var Γ β} → ρ x ≡ σ x) → sp < ρ , u > ≡ sp < σ , u >
  <>-ren-cong {sp = ∙} p = refl
  <>-ren-cong {sp = x , sp} p = cong₂ _,_ ([]-ren-cong {t = x} p) (<>-ren-cong p)


-- 2. The pre-renaming rule
mutual
  []-pre-ren : ∀{Γ Δ Ω α β}{t : SNf Γ α}{ρ : Ren Γ Δ}{σ : Ren Δ (Ω , β)}{u : SNf Ω β} → 
    (renSNf t ρ) [ σ , u ] ≡ t [ σ ∘ ρ , u ]
  []-pre-ren {t = lam t} = cong lam 
    (trans ([]-pre-ren {t = t}) 
    ([]-ren-cong {t = t} (cong sw (sym ext-∘))))
  []-pre-ren  {t = neu (x , sp)} {ρ = ρ} {σ = σ} with σ (ρ x)
  ... | vz = cong₂ _$_ refl (<>-pre-ren {sp = sp})
  ... | vs y = cong (λ z → neu (y , z)) <>-pre-ren
  
  <>-pre-ren : ∀{Γ Δ Ω α β γ}{sp : Sp Γ α γ}{ρ : Ren Γ Δ}{σ : Ren Δ (Ω , β)}{u : SNf Ω β} → 
    (renSp sp ρ) < σ , u > ≡ sp < σ ∘ ρ , u >
  <>-pre-ren {sp = ∙} = refl
  <>-pre-ren {sp = t , sp} = cong₂ _,_ ([]-pre-ren {t = t}) <>-pre-ren
  

-- 3. The post-renaming rule
mutual
  []-post-ren : ∀{Γ Δ Ω α β}(t : SNf Γ α)(ρ : Ren Γ (Δ , β))(u : SNf Δ β) →
    (σ : Ren Δ Ω) → t [ ext σ ∘ ρ , renSNf u σ ] ≡ renSNf (t [ ρ , u ]) σ 
  []-post-ren (lam t) ρ u σ = cong lam 
    (trans 
      (trans ([]-ren-cong {t = t} ren-lem) 
      (cong (λ z → t [ ext (ext σ) ∘ (sw ∘ ext ρ) , z ]) 
      (trans (sym renSNf-∘) renSNf-∘))) 
    ([]-post-ren t (sw ∘ ext ρ) (renSNf u vs) (ext σ)))
    where
      ren-lem : ∀{Γ Δ Ω α β}{ρ : Ren Γ (Δ , β)}{σ : Ren Δ Ω}{β' : Ty} {x : Var (Γ , α) β'} →
        (sw ∘ ext (ext σ ∘ ρ)) x ≡ (ext (ext σ) ∘ (sw ∘ ext ρ)) x
      ren-lem {x = vz} = refl
      ren-lem {ρ = ρ} {x = vs x} with ρ x
      ... | vz = refl
      ... | vs y = refl  
  []-post-ren (neu (x , sp)) ρ u σ with ρ x
  ... | vz = $-ren u sp ρ u σ
  ... | vs y = cong (λ z → neu (σ y , z)) (<>-post-ren sp ρ u σ)

  <>-post-ren : ∀{Γ Δ Ω α β γ}(sp : Sp Γ α γ)(ρ : Ren Γ (Δ , β))(u : SNf Δ β)(σ : Ren Δ Ω) →
    sp < ext σ ∘ ρ , renSNf u σ > ≡ renSp (sp < ρ , u >) σ
  <>-post-ren ∙ ρ u σ = refl
  <>-post-ren (t , sp) ρ u σ = cong₂ _,_ ([]-post-ren t ρ u σ) (<>-post-ren sp ρ u σ)

  $-ren : ∀{Γ Δ Ω α β γ}(t : SNf Δ α)(sp : Sp Γ α γ)(ρ : Ren Γ (Δ , β))(u : SNf Δ β)(σ : Ren Δ Ω) → 
    ((renSNf t σ) $ (sp < ext σ ∘ ρ , renSNf u σ >)) ≡ renSNf (t $ (sp < ρ , u >)) σ
  $-ren t ∙ ρ u σ = refl
  $-ren t (s , sp) ρ u σ = 
    trans 
      (cong (λ z → z $ (sp < ext σ ∘ ρ , renSNf u σ >)) 
        (trans (cong (λ z → napp (renSNf t σ) z) ([]-post-ren s ρ u σ)) (napp-ren t (s [ ρ , u ]) σ)))
    ($-ren (napp t (s [ ρ , u ])) sp ρ u σ)

  napp-ren : ∀{Γ Δ α β}(s : SNf Γ (α ⇒ β))(t : SNf Γ α)(ρ : Ren Γ Δ) →
    napp (renSNf s ρ) (renSNf t ρ) ≡ renSNf (napp s t) ρ
  napp-ren (lam s) t ρ = trans ([]-pre-ren {t = s}) ([]-post-ren s id t ρ)

-------------------------------------

-- 4. Normalization commutes with renaming
nf-ren : ∀{Γ Δ α} → (t : Tm Γ α) → (ρ : Ren Γ Δ) →
  snf (ren t ρ) ≡ renSNf (snf t) ρ
nf-ren {α = α} (var x) ρ = sym (nvar-ren x ρ)
nf-ren (lam t) ρ rewrite nf-ren t (ext ρ) = refl
nf-ren (app s t) ρ = trans (cong₂ napp (nf-ren s ρ) (nf-ren t ρ)) (napp-ren (snf s) (snf t) ρ)

-------------------------------------

-- 5. The empty substitution rule
-- Weaken a term then do a substitution on the weakened variable
-- is the same as doing nothing
mutual
  []-vs-id : ∀{Γ Δ α β}(u : SNf Γ α)(ρ : Ren Γ Δ)(t : SNf Δ β) → 
    u [ vs ∘ ρ , t ] ≡ renSNf u ρ
  []-vs-id (lam u) ρ t = cong lam (trans ([]-ren-cong {t = u} lem) ([]-vs-id _ _ _))
    where
      lem : ∀{Γ Δ α β γ}{ρ : Ren Γ Δ}{x : Var (Γ , α) γ} → 
        (sw ∘ ext (vs ∘ ρ)) x ≡ ((vs {β = β}) ∘ ext ρ) x
      lem {x = vz} = refl
      lem {x = vs x} = refl
  []-vs-id (neu (x , sp)) ρ t rewrite <>-vs-id sp ρ t = refl

  <>-vs-id : ∀{Γ Δ α1 α2 β}(sp : Sp Γ α1 α2)(ρ : Ren Γ Δ)(t : SNf Δ β) → 
    sp < vs ∘ ρ , t > ≡ renSp sp ρ
  <>-vs-id ∙ ρ t = refl
  <>-vs-id (x , sp) ρ t = cong₂ _,_ ([]-vs-id _ _ _) (<>-vs-id _ _ _)


-- 6. The commutative rule
-- This is about how to correctly swap the order of two consecutive substitutions

-- a special case of post-renaming rule
[]-post-ren-wk : ∀{Γ Δ α β γ}{t : SNf Γ α}{ρ : Ren Γ (Δ , β)}{u : SNf Δ β} → 
  wkSNf {α = γ} (t [ ρ , u ]) ≡ (wkSNf t) [ sw ∘ ext ρ , wkSNf u ]
[]-post-ren-wk {t = t} {ρ = ρ} = 
  trans (sym ([]-post-ren t _ _ _)) 
  (trans ([]-ren-cong {t = t} (sw-ext {ρ = ρ})) (sym ([]-pre-ren {t = t})))

-- the commutative lemma
mutual
  []-comm : 
    ∀{Γ Δ Ω α β1 β2}
    (s : SNf Γ α)(ρ : Ren Γ (Δ , β1))(t : SNf Δ β1)
    (σ : Ren Δ (Ω , β2))(u : SNf Ω β2) → 
      (s [ ρ , t ]) [ σ , u ] 
    ≡ (s [ (sw ∘ ext σ ∘ ρ) , wkSNf u ] )  [ id , t [ σ , u ] ]
  []-comm (lam s) ρ t σ u = 
    cong lam 
    (trans ([]-comm s _ _ _ _) 
    (trans (cong
      (λ z → (s [ sw ∘ ext (sw ∘ ext σ) ∘ sw ∘ ext ρ , wkSNf (wkSNf u) ]) [ id , z ])
      (sym ([]-post-ren-wk {t = t}) )) 
    (trans 
      (cong (λ z → z [ id , _ ]) 
      (trans ([]-ren-cong {t = s} lem1) 
      (trans (cong (λ z → s [ _ , z ]) 
        (trans (sym renSNf-∘) 
        (trans (renSNf-cong lem2) 
        (trans renSNf-∘ renSNf-∘))))
      ([]-post-ren s _ _ _))))
    ([]-pre-ren {t = s [ _ , _ ]} ) )))
    where 
      lem1 : ∀{Γ Δ Ω α β1 β2 γ}
          {ρ : Ren Γ (Δ , β1)}{σ : Ren Δ (Ω , β2)}
          {x : Var (Γ , α) γ} → 
          (sw ∘ ext (sw ∘ ext σ) ∘ sw ∘ ext ρ) x 
        ≡ (ext (sw ∘ ext id) ∘ sw ∘ ext (sw ∘ ext σ ∘ ρ)) x 
      lem1 {x = vz} = refl
      lem1 {ρ = ρ} {σ} {vs x} with ρ x
      ... | vz = refl
      ... | vs y with σ y
      ...         | vz = refl
      ...         | vs z = refl

      lem2 : ∀{Γ α1 α0 α}{x : Var Γ α} → ((vs {β = α0}) ∘ (vs {β = α1})) x ≡ (((sw ∘ ext id)) ∘ vs ∘ vs) x
      lem2 {x = vz} = refl
      lem2 {x = vs vz} = refl
      lem2 {x = vs (vs x)} = refl
  []-comm (neu (x , sp)) ρ t σ u with ρ x
  ... | vz rewrite 
      $-comm t (sp < ρ , t >) σ u 
    | <>-comm sp ρ t σ u
    = refl
  ... | vs y with σ y
  ... | vz rewrite 
      $-comm (renSNf u vs) (sp < sw ∘ ext σ ∘ ρ , renSNf u vs >) id (t [ σ , u ])
    | <>-comm sp ρ t σ u
    = cong (λ z → z $ ((sp < _ , _ >) < id , t [ σ , u ] >)) 
      (sym 
        (trans ([]-pre-ren {t = u}) 
        (trans ([]-vs-id u id _) renSNf-id)))
  ... | vs z rewrite <>-comm sp ρ t σ u = refl

  <>-comm : 
    ∀{Γ Δ Ω α1 α2 β1 β2}
      (sp : Sp Γ α1 α2)(ρ : Ren Γ (Δ , β1))(t : SNf Δ β1)
      (σ : Ren Δ (Ω , β2))(u : SNf Ω β2) → 
      (sp < ρ , t >) < σ , u > 
    ≡ (sp < (sw ∘ ext σ ∘ ρ) , wkSNf u >) < id , t [ σ , u ] >
  <>-comm ∙ ρ t σ u = refl
  <>-comm (s , sp) ρ t σ u = cong₂ _,_ ([]-comm s _ _ _ _) (<>-comm sp _ _ _ _)

  $-comm : ∀{Γ Δ α1 α2 β}(s : SNf Γ α1)(sp : Sp Γ α1 α2)(ρ : Ren Γ (Δ , β))(t : SNf Δ β) → 
    (s $ sp) [ ρ , t ] ≡ (s [ ρ , t ]) $ (sp < ρ , t >)
  $-comm s ∙ ρ t = refl
  $-comm s (x , sp) ρ t rewrite 
      $-comm (napp s x) sp ρ t
    | napp-comm s x ρ t
    = refl

  napp-comm : ∀{Γ Δ α β γ}(s : SNf Γ (α ⇒ β))(t : SNf Γ α)(ρ : Ren Γ (Δ , γ))(u : SNf Δ γ) → 
    (napp s t) [ ρ , u ] ≡ napp (s [ ρ , u ]) (t [ ρ , u ])
  napp-comm (lam s) t ρ u = []-comm s id _ _ _
