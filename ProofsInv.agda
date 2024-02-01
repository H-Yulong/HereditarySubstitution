module ProofsInv where

open import Spine
open import Lemmas

-------------------------------------

-- Updated version of proofs,
-- using inverses of β and η, removed sym.

{- Embedding of normal forms into terms -}
mutual
  embSNf : ∀{Γ σ} → SNf Γ σ → Tm Γ σ
  embSNf (lam t) = lam (embSNf t)
  embSNf (neu u) = embSNe u

  embSNe : ∀{Γ σ} → SNe Γ σ → Tm Γ σ
  embSNe (x , sp) = embSp sp (var x)

  embSp : ∀{Γ σ τ} → Sp Γ σ τ → Tm Γ σ → Tm Γ τ
  embSp ∙ acc = acc
  embSp (t , sp) acc = embSp sp (app acc (embSNf t))

-------------------------------------


{- Proof of completeness: terms are equivalent to their normal forms -}

-- equal terms are equivalent
Tm≡ : ∀{Γ α}{t u : Tm Γ α} → t ≡ u → t ≡t u
Tm≡ refl = idᵗ

-- congruence of terms for embSp
embSp-cong : ∀{Γ α β}{t u : Tm Γ α} → (sp : Sp Γ α β) → 
  t ≡t u → embSp sp t ≡t embSp sp u 
embSp-cong ∙ p = p
embSp-cong (x , sp) p = embSp-cong sp (p -$- idᵗ)

-- renamings commutes with embSNf
mutual
  renSNf-emb : ∀{Γ Δ α} → (t : SNf Γ α) → (ρ : Ren Γ Δ) → 
    embSNf (renSNf t ρ) ≡ ren (embSNf t) ρ
  renSNf-emb (lam t) ρ rewrite renSNf-emb t (ext ρ) = refl
  renSNf-emb (neu (x , sp)) ρ = renSp-emb sp (var x) ρ

  renSp-emb : ∀{Γ Δ α β} → (sp : Sp Γ α β) → (t : Tm Γ α) → (ρ : Ren Γ Δ) → 
    embSp (renSp sp ρ) (ren t ρ) ≡ ren (embSp sp t) ρ
  renSp-emb ∙ t ρ = refl
  renSp-emb (s , sp) t ρ rewrite renSNf-emb s ρ = trans refl (renSp-emb sp (app t (embSNf s)) ρ)

-- appSp preserves equivalence
appSp-comp : ∀{Γ α β γ} → (sp : Sp Γ α (β ⇒ γ)) → (u : Tm Γ α) → (t : SNf Γ β) → 
  embSp (appSp sp t) u ≡ app (embSp sp u) (embSNf t)
appSp-comp ∙ u t = refl
appSp-comp (x , sp) u t = appSp-comp sp (app u (embSNf x)) t


-- η-expansion preserves equivalence
ne2nf-comp : ∀{Γ α} → (u : SNe Γ α) → embSNf (ne2nf u) ≡t embSNe u 
ne2nf-comp {α = ι} u = idᵗ
ne2nf-comp {α = α ⇒ β} (x , sp) = 
  (λt (
    ne2nf-comp _ 
    => Tm≡ (appSp-comp (wkSp sp) _ _) 
    => ((Tm≡ (renSp-emb sp _ _)) -$- (ne2nf-comp _)))
  ) 
  => ≡η⁻¹

nvar-comp : ∀{Γ α} → (x : Var Γ α) → embSNf (nvar x) ≡t var x
nvar-comp x = ne2nf-comp (x , ∙)

-- the four hereditary substitution functions preserve equivalence
mutual
  []-comp : ∀{Γ Δ α β} → (t : SNf Γ α)→ (ρ : Ren Γ (Δ , β)) → (u : SNf Δ β) → 
    embSNf (t [ ρ , u ]) ≡t ((embSNf t) [ ρ , embSNf u ]Tm)
  []-comp (lam t) ρ u = 
    λt 
      (coerce (renSNf-emb u vs) 
        (λ z → embSNf (t [ sw ∘ ext ρ , renSNf u vs ]) ≡t ((embSNf t) [ (sw ∘ ext ρ) , z ]Tm)) 
        ([]-comp t (sw ∘ ext ρ) (wkSNf u)))
  []-comp (neu (x , sp)) ρ u with ρ x in eq
  ... | vz rewrite eq = 
    ($-comp u (sp < ρ , u >)) 
    => embSp-cong (sp < ρ , u >) (Tm≡ (sym ([]Tm-vz {ρ = ρ} eq))) 
    => <>-comp sp ρ u (var x)
  ... | vs y = 
    embSp-cong (sp < ρ , u >) (Tm≡ (sym ([]Tm-vs {ρ = ρ} {t = embSNf u} eq))) 
    => <>-comp sp ρ u (var x)

  <>-comp : ∀{Γ Δ α β γ} → (sp : Sp Γ α γ) → (ρ : Ren Γ (Δ , β)) → (u : SNf Δ β) → 
    (z : Tm Γ α) → embSp (sp < ρ , u >) (z [ ρ , embSNf u ]Tm) ≡t ((embSp sp z) [ ρ , embSNf u ]Tm)
  <>-comp ∙ ρ u z = idᵗ
  <>-comp (t , sp) ρ u z = 
    embSp-cong (sp < ρ , u >) (idᵗ -$- ([]-comp t ρ u))
    => <>-comp sp ρ u (app z (embSNf t))

  $-comp : ∀{Γ α β} → (t : SNf Γ α) → (sp : Sp Γ α β) →
    embSNf (t $ sp) ≡t embSp sp (embSNf t)
  $-comp t ∙ = idᵗ
  $-comp t (u , sp) = ($-comp (napp t u) sp) => (embSp-cong sp (napp-comp t u))

  napp-comp : ∀{Γ α β} → (s : SNf Γ (α ⇒ β)) → (t : SNf Γ α) → 
    embSNf (napp s t) ≡t app (embSNf s) (embSNf t)
  napp-comp (lam s) t = ([]-comp s id t) => ≡β⁻¹

-- The completeness theorem
completeness : ∀{Γ α} → (t : Tm Γ α) → embSNf (snf t) ≡t t
completeness (var x) = nvar-comp x
completeness (lam t) = λt (completeness t)
completeness (app s t) = (napp-comp (snf s) (snf t)) => ((completeness s) -$- (completeness t))



-------------------------------------

{- Proof of soundness: equivalent terms have equal normal forms -}

-- There are two main goals here.
-- 1. Show the η-expansion identity: a term and its η-expanded version have the same normal form.
-- 2. Show that substitution on terms commutes with hereditary substitutions on normal forms.

-------------------------------------

{- 1. Proof of η-expansion identity -}

{- A few lemmas -}

-- appSp with hereditary substitution
appSp-<> : ∀{Γ Δ α β γ τ}{sp : Sp Γ γ (α ⇒ β)}{t : SNf Γ α}{ρ : Ren Γ (Δ , τ)}{u : SNf Δ τ} → 
  (appSp sp t) < ρ , u > ≡ appSp (sp < ρ , u >) (t [ ρ , u ])
appSp-<> {sp = ∙} = refl
appSp-<> {sp = x , sp} {t} {ρ} {u}
  rewrite appSp-<> {sp = sp} {t} {ρ} {u} = refl

-- special cases of post-renaming rule
wk-[sw∘ext] : ∀{Γ Δ α β τ}{t : SNf Γ α}{ρ : Ren Γ (Δ , β)}{u : SNf Δ β} → 
  (wkSNf {α = τ} t) [ sw ∘ ext ρ , wkSNf u ] ≡ wkSNf (t [ ρ , u ])
wk-[sw∘ext] {t = t} {ρ} = 
  trans ([]-pre-ren {t = t}) 
  (trans ([]-ren-cong {t = t} (sym (sw-ext {ρ = ρ}))) ([]-post-ren t _ _ _))

wk-<sw∘ext> : ∀{Γ Δ α β γ τ}{sp : Sp Γ α γ}{ρ : Ren Γ (Δ , β)}{u : SNf Δ β} → 
  (wkSp {α = τ} sp) < sw ∘ ext ρ , wkSNf u > ≡ wkSp (sp < ρ , u >)
wk-<sw∘ext> {sp = sp} {ρ} = 
  trans (<>-pre-ren {sp = sp}) 
  (trans (<>-ren-cong{sp = sp} (sym (sw-ext {ρ = ρ}))) (<>-post-ren _ _ _ _))

-- We show vs case first, as it is required later
ne2nf-[]-vs : ∀{Γ Δ α β γ}
  {x : Var Γ α}{sp : Sp Γ α β}{ρ : Ren Γ (Δ , γ)}{u : SNf Δ γ} → 
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
nvar-wk-sw : ∀{Γ α β} → wkSNf {Γ , α} {β} (nvar vz) ≡ renSNf (nvar vz) sw
nvar-wk-sw {Γ} {α} {β} = trans (nvar-ren vz vs) (sym (nvar-ren vz sw))

-- the η-expansion identity lemma, in a more general case
mutual 
  η-eq-[] : ∀{Γ Δ α β}(u : SNf Γ α)(ρ : Ren Γ (Δ , β)) → 
    u [ ext {α = β} vs ∘ ρ , nvar vz ] ≡ renSNf u ρ
  η-eq-[] (lam u) ρ = cong lam 
    -- = u [ sw ∘ ext(ext vs) ∘ ext ρ , wkSNf (nvar vz) ]
    (trans (cong (λ z → u [ sw ∘ ext (ext vs ∘ ρ) , z ]) nvar-wk-sw)
    -- = u [ sw ∘ ext(ext vs) ∘ ext ρ , renSNf (nvar vz) sw ] 
    (trans ([]-ren-cong {t = u} {σ = ext sw ∘ ext vs ∘ sw ∘ ext ρ}
      -- proof of that two renamings are equal 
      (trans (cong sw (ext-∘ {σ = ext vs})) 
      (trans (sym ext2-sw) 
      (trans (ext-∀ (sw-ext {ρ = id})) ext-∘)))) 
    -- = u [ ext sw ∘ ext vs ∘ sw ∘ ext ρ , ... ] 
    (trans ([]-post-ren u _ _ _) 
    -- = renSNf (u [ ext vs ∘ sw ∘ ext ρ , nvar vz ]) sw
    (trans (cong (λ z → renSNf z sw) (η-eq-[] u (sw ∘ ext ρ))) 
    -- = renSNf (renSNf u (sw ∘ ext ρ)) sw
    (trans (sym renSNf-∘) (renSNf-cong sw-sw-id))))))
    -- = renSNf u (ext ρ)
  η-eq-[] (neu (x , sp)) ρ with ρ x
  ... | vz rewrite η-eq-<> sp ρ = η-eq-$ vz ∙ (renSp sp ρ)
  ... | vs y = cong (λ z → neu (vs y , z)) (η-eq-<> sp ρ)

  η-eq-<> : ∀{Γ Δ α β γ}(sp : Sp Γ α γ)(ρ : Ren Γ (Δ , β)) → 
    sp < ext vs ∘ ρ , nvar vz > ≡ renSp sp ρ
  η-eq-<> ∙ ρ = refl
  η-eq-<> (s , sp) ρ = cong₂ _,_ (η-eq-[] s ρ) (η-eq-<> sp ρ)

  η-eq-$ : ∀{Γ α β}(x : Var Γ α)(sp : Sp Γ α β)(sp' : Sp Γ β ι) → 
    (ne2nf (x , sp)) $ sp' ≡ ne2nf (x , sp ++ sp')
  η-eq-$ x sp ∙ rewrite ++-z {sp = sp} = refl
  η-eq-$ x sp (s' , sp') = 
    trans (cong (λ z → z $ sp') (η-eq-napp _ _ _)) 
    (trans (η-eq-$ x (appSp sp s') sp') 
    (cong (λ z → neu (x , z)) (appSp-++ _ _ _)))

-- used ne2nf-[]-vz mutual recursively here 
-- to show that (nvar vz) [ id , s ] ≡ s
-- it seems natural to do this here, not sure why / how to explain
  η-eq-napp : ∀{Γ α β γ}(x : Var Γ α)(sp : Sp Γ α (β ⇒ γ))(s : SNf Γ β) → 
    napp (ne2nf (x , sp)) s ≡ ne2nf (x , appSp sp s)
  η-eq-napp x sp s = 
    trans (ne2nf-[]-vs refl) 
    (cong (λ z → ne2nf (x , z)) 
      (trans appSp-<> 
      (cong₂ appSp 
        (trans <>-pre-ren (trans (<>-vs-id _ _ _) renSp-id))
        (ne2nf-[]-vz refl))))

  lam-$-id : ∀{Γ α β γ}{u : SNf Γ α}{sp : Sp Γ α (β ⇒ γ)} → 
    lam (wkSNf u $ (appSp (wkSp sp) (nvar vz))) ≡ u $ sp
  lam-$-id {β = β} {u = lam u} {sp = ∙} =  cong lam 
    (trans ([]-pre-ren {t = u}) 
    (trans ([]-ren-cong {t = u} {σ = ext vs ∘ id} refl) 
    (trans (η-eq-[] u id) renSNf-id)))
  lam-$-id {β = β} {u = lam u} {sp = s , sp} = 
    trans  
      (cong lam 
        (cong₂ _$_ {u = appSp (wkSp sp) (nvar vz)} (napp-ren (lam u) s vs) refl)) 
      (lam-$-id {u = napp (lam u) s} {sp = sp})

  -- As you can see, it needs ne2nf-[]-vs to show that (nvar vz) [ sw ∘ ext ρ , u ] = nvar vz,
  -- since (sw ∘ ext ρ) vz = vs vz.
  ne2nf-[]-vz : ∀{Γ Δ α β}
    {x : Var Γ α}{sp : Sp Γ α β}{ρ : Ren Γ (Δ , α)}{u : SNf Δ α} → 
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

-- the η-expansion identity lemma
nf-η : ∀{Γ α β} → (u : Tm Γ (α ⇒ β)) → lam (napp (snf (wk u)) (nvar vz)) ≡ snf u
nf-η u with snf u in eq
... | lam v = cong lam 
  (trans (cong (λ z → napp z (nvar vz)) 
    (trans (nf-ren u vs) (cong (λ z → renSNf z vs) eq))) 
  (trans ([]-pre-ren {t = v}) 
  (trans ([]-ren-cong {t = v} {σ = ext vs ∘ id} refl) 
  (trans (η-eq-[] v _) renSNf-id))))

-------------------------------------

{- 2. Proof of commuting substitutions -}

nf-sub : ∀{Γ Δ α β} → (t : Tm Γ α) → (ρ : Ren Γ (Δ , β)) → (u : Tm Δ β) →  
  snf t [ ρ , snf u ] ≡ snf (t [ ρ , u ]Tm)
nf-sub (var x) ρ u with ρ x in eq
... | vz = ne2nf-[]-vz eq
... | vs y = ne2nf-[]-vs eq
nf-sub {β = β} (lam t) ρ u = 
  cong lam 
    (trans 
      (cong (λ z → snf t [ sw ∘ ext ρ , z ]) (sym (nf-ren u vs))) 
      (nf-sub t (sw ∘ ext ρ) (wk u)))
nf-sub (app s t) ρ u =
  trans 
    (napp-comm (snf s) (snf t) ρ (snf u)) 
    (cong₂ napp (nf-sub s ρ u) (nf-sub t ρ u))

-------------------------------------
soundness : ∀{Γ α}{t u : Tm Γ α} → t ≡t u → snf t ≡ snf u
soundness {t = t} ≡η = sym (nf-η t)
soundness {u = u} ≡η⁻¹ = nf-η u
soundness {t = app (lam t) u} ≡β = nf-sub t id u
soundness {u = app (lam t) u} ≡β⁻¹ = sym (nf-sub t id u)
soundness idᵗ = refl
soundness (p => p') = trans (soundness p) (soundness p')
soundness (λt p) rewrite soundness p = refl
soundness (p -$- p') rewrite soundness p | soundness p' = refl

-------------------------------------

-- Normalization is idempotent on terms
idemS : ∀{Γ α}(t : Tm Γ α) → snf (embSNf (snf t)) ≡ snf t
idemS t = soundness (completeness t)

mutual 
  -- Normalization is idempotent on normal forms
  embSNf-nf : ∀{Γ α}(t : SNf Γ α) → snf (embSNf t) ≡ t
  embSNf-nf (lam t) = cong lam (embSNf-nf t)
  embSNf-nf (neu (x , ∙)) = refl
  embSNf-nf (neu (x , (s , sp))) = 
    trans (embSp-nf (app (var x) (embSNf s)) sp) 
    (trans (cong (λ z → z $ sp) (ne2nf-[]-vs refl)) 
    (trans (η-eq-$ x (_ , ∙) sp) 
    (cong (λ z → neu (x , (z , sp))) (trans (ne2nf-[]-vz refl) (embSNf-nf s)))))

  embSp-nf : ∀{Γ α β}(t : Tm Γ α)(sp : Sp Γ α β) → snf (embSp sp t) ≡ (snf t) $ sp
  embSp-nf t ∙ = refl
  embSp-nf t (s , sp) = 
    trans (embSp-nf (app t (embSNf s)) sp) 
    (cong (λ z → napp (snf t) z $ sp) (embSNf-nf s))

-- Hence, uniqueness of normal forms
uniqueS : ∀{Γ α} → (t1 t2 : SNf Γ α) → embSNf t1 ≡t embSNf t2 → t1 ≡ t2
uniqueS t1 t2 p = trans (sym (embSNf-nf t1)) (trans (soundness p) (embSNf-nf t2))
 
-------------------------------------

-- Investigation on completeness derivations

c1 : embSNf (snf t1) ≡t t1
c1 = idᵗ

c2 : t2 ≡t embSNf (snf t2)
c2 = ≡η => λt ((idᵗ -$- ≡η) => ≡η)
-- \g. \x. f (\y. g y) x = \g. f (\y. g y) = \g. f g = f
-- λt (≡η⁻¹ => (app-t idᵗ ≡η⁻¹)) => ≡η⁻¹

c2' : t2 ≡t embSNf (snf t2)
c2' = ≡η => λt (≡η => λt (idᵗ -$- ≡η -$- idᵗ))

inv : ∀{Γ α}{t u : Tm Γ α} → t ≡t u → u ≡t t
inv ≡β = ≡β⁻¹
inv ≡η = ≡η⁻¹
inv ≡β⁻¹ = ≡β
inv ≡η⁻¹ = ≡η
inv idᵗ = idᵗ
inv (p => p') = inv p' => inv p
inv (λt p) = λt (inv p)
inv (p -$- p') = (inv p) -$- (inv p')

-- A hack of simplifying derivation trees
normPf : ∀{Γ α}{t1 t2 : Tm Γ α} → t1 ≡t t2 → t1 ≡t t2
normPf ≡β = ≡β
normPf ≡η = ≡η
normPf ≡β⁻¹ = ≡β⁻¹
normPf ≡η⁻¹ = ≡η⁻¹
normPf idᵗ = idᵗ
normPf (p1 => p2) with normPf p1 
normPf (p1 => p2) | idᵗ = normPf p2
normPf (p1 => p2) | p1' with normPf p2
normPf (p1 => p2) | p1' | idᵗ = p1'
normPf (p1 => p2) | p1' | p2' = p1' => p2'
normPf (λt p) with normPf p
... | idᵗ = idᵗ
... | p' = λt p'
normPf (p1 -$- p2) with normPf p1 | normPf p2
... | idᵗ | idᵗ = idᵗ
... | p1' | p2' = p1' -$- p2'

transform : ∀{Γ α} → (t : Tm Γ α) → t ≡t embSNf (snf t)
transform t = inv (normPf (completeness t))

