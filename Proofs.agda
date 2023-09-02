module Proofs where

open import Hereditary
open import Lemmas

-------------------------------------

{- βη-equality -}
data _≡t_ : ∀{Γ α} → Tm Γ α → Tm Γ α → Set where
  ≡β : ∀{Γ α β}{t : Tm (Γ , α) β}{u : Tm Γ α} → app (lam t) u ≡t (t [ u ]0)
  ≡η : ∀{Γ α β}{t : Tm Γ (α ⇒ β)} → lam (app (wk t) (var vz)) ≡t t
  -- reflexive, symmetry, transitivity
  refl-t : ∀{Γ α}{t : Tm Γ α} → t ≡t t
  sym-t : ∀{Γ α}{t u : Tm Γ α} → t ≡t u → u ≡t t  
  tran-t : ∀{Γ α}{t u v : Tm Γ α} → t ≡t u → u ≡t v → t ≡t v
  -- congruence under lam and app
  lam-t : ∀{Γ α β}{t u : Tm (Γ , α) β} → t ≡t u → lam t ≡t lam u
  app-t : ∀{Γ α β}{t t' : Tm Γ (α ⇒ β)}{u u' : Tm Γ α} → 
      t ≡t t' → u ≡t u' → app t u ≡t app t' u'


{- Embedding of normal forms into terms -}
mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf tt = tt
  embNf (lam t) = lam (embNf t)
  embNf (neu u) = embNe u

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (x , sp) = embSp sp (var x)

  embSp : ∀{Γ σ τ} → Sp Γ σ τ → Tm Γ σ → Tm Γ τ
  embSp ∙ acc = acc
  embSp (t , sp) acc = embSp sp (app acc (embNf t))

-------------------------------------

{- Proof of completeness: terms are equivalent to their normal forms -}

-- equal terms are equivalent
Tm≡ : ∀{Γ α}{t u : Tm Γ α} → t ≡ u → t ≡t u
Tm≡ refl = refl-t

-- congruence of terms for embSp
embSp-cong : ∀{Γ α β}{t u : Tm Γ α} → (sp : Sp Γ α β) → 
  t ≡t u → embSp sp t ≡t embSp sp u 
embSp-cong ∙ p = p
embSp-cong (x , sp) p = embSp-cong sp (app-t p refl-t)

-- renamings commutes with embNf
mutual
  renNf≡ : ∀{Γ Δ α} → (t : Nf Γ α) → (ρ : Ren Γ Δ) → 
    embNf (renNf t ρ) ≡ ren (embNf t) ρ
  renNf≡ tt ρ = refl
  renNf≡ (lam t) ρ rewrite renNf≡ t (ext ρ) = refl
  renNf≡ (neu (x , sp)) ρ = renSp≡ sp (var x) ρ

  renSp≡ : ∀{Γ Δ α β} → (sp : Sp Γ α β) → (t : Tm Γ α) → (ρ : Ren Γ Δ) → 
    embSp (renSp sp ρ) (ren t ρ) ≡ ren (embSp sp t) ρ
  renSp≡ ∙ t ρ = refl
  renSp≡ (s , sp) t ρ rewrite renNf≡ s ρ = trans refl (renSp≡ sp (app t (embNf s)) ρ)

-- appSp interacts with embSp, embNf
appSp≡ : ∀{Γ α β γ} → (sp : Sp Γ α (β ⇒ γ)) → (u : Tm Γ α) → (t : Nf Γ β) → 
  app (embSp sp u) (embNf t) ≡ embSp (appSp sp t) u
appSp≡ ∙ u t = refl
appSp≡ (x , sp) u t = appSp≡ sp (app u (embNf x)) t

-- η-expansion preserves equivalence
ne2nf-comp : ∀{Γ α} → (u : Ne Γ α) → embNf (ne2nf u) ≡t embNe u 
ne2nf-comp {α = ι} u = refl-t
ne2nf-comp {α = α ⇒ β} (x , sp) = 
    tran-t (lam-t (ne2nf-comp (vs x , appSp (renSp sp vs) (ne2nf (vz , ∙))))) 
  (tran-t (lam-t (sym-t (Tm≡ (appSp≡ (renSp sp vs) (var (vs x)) (ne2nf (vz , ∙))))))
  (tran-t (lam-t (app-t (Tm≡ (renSp≡ sp (var x) vs)) (ne2nf-comp (vz , ∙)))) ≡η))

nvar-comp : ∀{Γ α} → (x : Var Γ α) → embNf (nvar x) ≡t var x
nvar-comp x = ne2nf-comp (x , ∙)

-- the four hereditary substitution functions preserves ≡t
mutual
  []-comp : ∀{Γ Δ α β} → (t : Nf Γ α)→ (ρ : Ren Γ (Δ , β)) → (u : Nf Δ β) → 
    embNf (t [ ρ , u ]) ≡t ((embNf t) [ ρ , embNf u ]Tm)
  []-comp tt ρ u = refl-t
  []-comp (lam t) ρ u = 
    lam-t 
      (coerce (renNf≡ u vs) 
        (λ z → embNf (t [ sw ∘ ext ρ , renNf u vs ]) ≡t ((embNf t) [ (sw ∘ ext ρ) , z ]Tm)) 
        ([]-comp t (sw ∘ ext ρ) (wkNf u)))
  []-comp (neu (x , sp)) ρ u with ρ x in eq
  ... | vz rewrite eq = 
    tran-t ($-comp u (sp < ρ , u >)) 
    (tran-t (embSp-cong (sp < ρ , u >) (sym-t (Tm≡ ([]Tm-vz {ρ = ρ} eq)))) 
    (<>-comp sp ρ u (var x)))
  ... | vs y = 
    tran-t (embSp-cong (sp < ρ , u >) (sym-t (Tm≡ ([]Tm-vs {ρ = ρ} eq)))) (<>-comp sp ρ u (var x))

  <>-comp : ∀{Γ Δ α β γ} → (sp : Sp Γ α γ) → (ρ : Ren Γ (Δ , β)) → (u : Nf Δ β) → 
    (z : Tm Γ α) → embSp (sp < ρ , u >) (z [ ρ , embNf u ]Tm) ≡t ((embSp sp z) [ ρ , embNf u ]Tm)
  <>-comp ∙ ρ u z = refl-t
  <>-comp (t , sp) ρ u z = 
    tran-t (embSp-cong (sp < ρ , u >) (app-t refl-t ([]-comp t ρ u))) 
    (<>-comp sp ρ u (app z (embNf t))) 

  $-comp : ∀{Γ α β} → (t : Nf Γ α) → (sp : Sp Γ α β) →
    embNf (t $ sp) ≡t embSp sp (embNf t)
  $-comp t ∙ = refl-t
  $-comp t (u , sp) = tran-t ($-comp (napp t u) sp) (embSp-cong sp (napp-comp t u))

  napp-comp : ∀{Γ α β} → (s : Nf Γ (α ⇒ β)) → (t : Nf Γ α) → 
    embNf (napp s t) ≡t app (embNf s) (embNf t)
  napp-comp (lam s) t = tran-t ([]-comp s id t) (sym-t ≡β)


completeness : ∀{Γ α} → (t : Tm Γ α) → embNf (nf t) ≡t t
completeness tt = refl-t
completeness (var x) = nvar-comp x
completeness (lam t) = lam-t (completeness t)
completeness (app s t) = tran-t (napp-comp (nf s) (nf t)) (app-t (completeness s) (completeness t))


-------------------------------------

{- Proof of soundness: equivalent terms has equal normal forms -}

-- There are two main goals here.
-- 1. Show the η-expansion identity.
-- 2. Show that substitution on terms commutes with hereditary substitutions on normal forms.

-------------------------------------

{- 1. Proof of η-expansion identity -}

{- A few lemmas -}

-- appSp with hereditary substitution
appSp-<> : ∀{Γ Δ α β γ τ}{sp : Sp Γ γ (α ⇒ β)}{t : Nf Γ α}{ρ : Ren Γ (Δ , τ)}{u : Nf Δ τ} → 
  (appSp sp t) < ρ , u > ≡ appSp (sp < ρ , u >) (t [ ρ , u ])
appSp-<> {sp = ∙} = refl
appSp-<> {sp = x , sp} {t} {ρ} {u}
  rewrite appSp-<> {sp = sp} {t} {ρ} {u} = refl

-- special cases of post-renaming rule
wk-[sw∘ext] : ∀{Γ Δ α β τ}{t : Nf Γ α}{ρ : Ren Γ (Δ , β)}{u : Nf Δ β} → 
  (wkNf {α = τ} t) [ sw ∘ ext ρ , wkNf u ] ≡ wkNf (t [ ρ , u ])
wk-[sw∘ext] {t = t} {ρ} = 
  trans ([]-pre-ren {t = t}) 
  (trans ([]-ren-cong {t = t} (sym (sw-ext {ρ = ρ}))) ([]-post-ren t _ _ _))

wk-<sw∘ext> : ∀{Γ Δ α β γ τ}{sp : Sp Γ α γ}{ρ : Ren Γ (Δ , β)}{u : Nf Δ β} → 
  (wkSp {α = τ} sp) < sw ∘ ext ρ , wkNf u > ≡ wkSp (sp < ρ , u >)
wk-<sw∘ext> {sp = sp} {ρ} = 
  trans (<>-pre-ren {sp = sp}) 
  (trans (<>-ren-cong{sp = sp} (sym (sw-ext {ρ = ρ}))) (<>-post-ren _ _ _ _))

-- We show vs case first, as it is required later
ne2nf-[]-vs : ∀{Γ Δ α β γ}
  {x : Var Γ α}{sp : Sp Γ α β}{ρ : Ren Γ (Δ , γ)}{u : Nf Δ γ} → 
  {y : Var Δ α} → ρ x ≡ vs y → ne2nf (x , sp) [ ρ , u ] ≡ ne2nf (y , sp < ρ , u >)
ne2nf-[]-vs {β = ι} p rewrite p = refl
ne2nf-[]-vs {β = β1 ⇒ β2} {x = x} {sp} {ρ} {u} {y} p rewrite p
  = cong lam 
    (trans (ne2nf-[]-vs {x = vs x} (cong (sw ∘ vs) p)) 
    (cong (λ z → ne2nf (vs y , z)) 
      (trans (appSp-<> {sp = renSp sp vs}) 
      (cong₂ appSp 
        (trans <>-pre-ren 
          (trans (<>-ren-cong(sym (sw-ext {ρ = ρ}))) (<>-post-ren _ _ _ _)))   
        (ne2nf-[]-vs refl)))))

-- a simple lemma to help the next big lemma
nvar-wk-sw : ∀{Γ α β} → wkNf {Γ , α} {β} (nvar vz) ≡ renNf (nvar vz) sw
nvar-wk-sw {Γ} {α} {β} = trans (nvar-ren vz vs) (sym (nvar-ren vz sw))

-- the η-expansion identity set
mutual 
  η-eq-[] : ∀{Γ Δ α β}(u : Nf Γ α)(ρ : Ren Γ (Δ , β)) → 
    u [ ext {α = β} vs ∘ ρ , nvar vz ] ≡ renNf u ρ
  η-eq-[] tt ρ = refl
  η-eq-[] (lam u) ρ = cong lam 
    -- = u [ sw ∘ ext(ext vs) ∘ ext ρ , wkNf (nvar vz) ] = u [ sw ∘ ext(ext vs) ∘ ext ρ , renNf (nvar vz) sw ]
    (trans (cong (λ z → u [ sw ∘ ext (ext vs ∘ ρ) , z ]) nvar-wk-sw)
    -- = u [ sw ∘ ext(ext vs) ∘ ext ρ , renNf (nvar vz) sw ] 
    (trans ([]-ren-cong {t = u} {σ = ext sw ∘ ext vs ∘ sw ∘ ext ρ}
      -- proof of that two renamings are equal 
      (trans (cong sw (ext-∘ {σ = ext vs})) 
      (trans (sym wk2-sw-assoc) 
      (trans (ext-∀ (sw-ext {ρ = id})) ext-∘)))) 
    -- = u [ ext sw ∘ ext vs ∘ sw ∘ ext ρ , ... ] 
    (trans ([]-post-ren u _ _ _) 
    -- = renNf (u [ ext vs ∘ sw ∘ ext ρ , nvar vz ]) sw
    (trans (cong (λ z → renNf z sw) (η-eq-[] u (sw ∘ ext ρ))) 
    -- = renNf (renNf u (sw ∘ ext ρ)) sw
    (trans (sym renNf-∘) (renNf-cong sw-sw-id))))))
    -- = renNf u (ext ρ)
  η-eq-[] (neu (x , sp)) ρ with ρ x
  ... | vz rewrite η-eq-<> sp ρ = η-eq-$ vz ∙ (renSp sp ρ)
  ... | vs y = cong (λ z → neu (vs y , z)) (η-eq-<> sp ρ)

  η-eq-<> : ∀{Γ Δ α β γ}(sp : Sp Γ α γ)(ρ : Ren Γ (Δ , β)) → 
    sp < ext vs ∘ ρ , nvar vz > ≡ renSp sp ρ
  η-eq-<> ∙ ρ = refl
  η-eq-<> (s , sp) ρ = cong₂ _,_ (η-eq-[] s ρ) (η-eq-<> sp ρ)

  η-eq-$ : ∀{Γ α β}(x : Var (Γ , α) α)(sp : Sp (Γ , α) α β)(sp' : Sp (Γ , α) β ι) → 
    (ne2nf (x , sp)) $ sp' ≡ ne2nf (x , sp ++ sp')
  η-eq-$ x sp ∙ rewrite ++-z {sp = sp} = refl
  η-eq-$ x sp (s' , sp') = 
    trans (cong (λ z → z $ sp') (η-eq-napp _ _ _)) 
    (trans (η-eq-$ x (appSp sp s') sp') 
    (cong (λ z → neu (x , z)) (appSp-++ _ _ _)))

-- used ne2nf-[]-vz mutual recursively here 
-- to show that (nvar vz) [ id , s ] ≡ s
-- it seems natural to do this here, not sure why / how to explain
  η-eq-napp : ∀{Γ α β γ}(x : Var (Γ , α) α)(sp : Sp (Γ , α) α (β ⇒ γ))(s : Nf (Γ , α) β) → 
    napp (ne2nf (x , sp)) s ≡ ne2nf (x , appSp sp s)
  η-eq-napp x sp s = 
    trans (ne2nf-[]-vs refl) 
    (cong (λ z → ne2nf (x , z)) 
      (trans appSp-<> 
      (cong₂ appSp 
        (trans <>-pre-ren (trans (<>-vs-id _ _ _) renSp-id))
        (ne2nf-[]-vz refl))))

  lam-$-id : ∀{Γ α β γ}{u : Nf Γ α}{sp : Sp Γ α (β ⇒ γ)} → 
    lam (wkNf u $ (appSp (wkSp sp) (nvar vz))) ≡ u $ sp
  lam-$-id {β = β} {u = lam u} {sp = ∙} =  cong lam 
    (trans ([]-pre-ren {t = u}) 
    (trans ([]-ren-cong {t = u} {σ = ext vs ∘ id} refl) 
    (trans (η-eq-[] u id) renNf-id)))
  lam-$-id {β = β} {u = lam u} {sp = s , sp} = 
    trans  
      (cong lam 
        (cong₂ _$_ {u = appSp (wkSp sp) (nvar vz)} (napp-ren≡ (lam u) s vs) refl)) 
      (lam-$-id {u = napp (lam u) s} {sp = sp})

  -- As you can see, it needs ne2nf-[]-vs to show that (nvar vz) [ sw ∘ ext ρ , u ] = nvar vz,
  -- since (sw ∘ ext ρ) vz = vs vz.
  ne2nf-[]-vz : ∀{Γ Δ α β}
    {x : Var Γ α}{sp : Sp Γ α β}{ρ : Ren Γ (Δ , α)}{u : Nf Δ α} → 
    ρ x ≡ vz → ne2nf (x , sp) [ ρ , u ] ≡ u $ (sp < ρ , u >)
  ne2nf-[]-vz {β = ι} p rewrite p = refl
  ne2nf-[]-vz {β = β1 ⇒ β2} {x} {sp} {ρ} {u} p = 
    trans 
      (cong lam 
        (trans (ne2nf-[]-vz (cong (sw ∘ vs) p))
        (cong₂ _$_ {v = appSp (wkSp (sp < ρ , u >)) (nvar vz)}
          refl 
          (trans appSp-<> (cong₂ appSp wk-<sw∘ext> (ne2nf-[]-vs refl))))))
      (lam-$-id {sp = sp < ρ , u >}) 

nf-η : ∀{Γ α β} → (u : Tm Γ (α ⇒ β)) → lam (napp (nf (wk u)) (nvar vz)) ≡ nf u
nf-η u with nf u in eq
... | lam v = cong lam 
  (trans (cong (λ z → napp z (nvar vz)) 
    (trans (nf-ren u vs) (cong (λ z → renNf z vs) eq))) 
  (trans ([]-pre-ren {t = v}) 
  (trans ([]-ren-cong {t = v} {σ = ext vs ∘ id} refl) 
  (trans (η-eq-[] v _) renNf-id))))

-------------------------------------

{- 2. Proof of commuting substitutions -}

nf-sub : ∀{Γ Δ α β} → (t : Tm Γ α) → (ρ : Ren Γ (Δ , β)) → (u : Tm Δ β) →  
  nf t [ ρ , nf u ] ≡ nf (t [ ρ , u ]Tm)
nf-sub tt ρ u = refl
nf-sub (var x) ρ u with ρ x in eq
... | vz = ne2nf-[]-vz eq
... | vs y = ne2nf-[]-vs eq
nf-sub {β = β} (lam t) ρ u = 
  cong lam 
    (trans 
      (cong (λ z → nf t [ sw ∘ ext ρ , z ]) (sym (nf-ren u vs))) 
      (nf-sub t (sw ∘ ext ρ) (wk u)))
nf-sub (app s t) ρ u =
  trans 
    (napp-comm (nf s) (nf t) ρ (nf u)) 
    (cong₂ napp (nf-sub s ρ u) (nf-sub t ρ u))

-------------------------------------

soundness : ∀{Γ α}{t u : Tm Γ α} → t ≡t u → nf t ≡ nf u
soundness {t = app (lam t) u} ≡β = nf-sub t id u
soundness {u = u} ≡η = nf-η u
soundness refl-t = refl
soundness (sym-t p) = sym (soundness p)
soundness (tran-t p p') = trans (soundness p) (soundness p')
soundness (lam-t p) rewrite soundness p = refl
soundness (app-t p p') rewrite soundness p | soundness p' = refl
 