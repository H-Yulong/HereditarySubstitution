module SProof where

open import Stack
open import Spine

open import ProofsInv using (embSNf; embSNe; embSp; Tm≡; soundness; idemS; embSNf-nf)

-- Note : everything here are very drafty,
-- and some of the things in the mutual block are 
-- totally unnecessary, should be factored out.

-- Nf is isomorphic to SNf

-- Nf -> SNf
mutual 
  toSNf : ∀{Γ α} → Nf Γ α → SNf Γ α
  toSNf (lam t) = lam (toSNf t)
  toSNf (↓ u) = neu (toSNe u)

  toSNe : ∀{Γ α} → Ne Γ α → SNe Γ α
  toSNe (var x) = x , ∙
  toSNe (app u t) = (toSNe u) $$sp (toSNf t , ∙)

-- SNf -> Nf
mutual 
  toNf : ∀{Γ α} → SNf Γ α → Nf Γ α
  toNf (lam t) = lam (toNf t)
  toNf (neu u) = ↓ (toNe u)

  toNe : ∀{Γ α} → SNe Γ α → Ne Γ α
  toNe (x , sp) = (var x) $$ toSt sp

  toSt : ∀{Γ α β} → Sp Γ α β → St Γ α β
  toSt ∙ = ∙
  toSt (s , st) = (toNf s) , (toSt st)

-- Two sides of isomorphism, along with some lemmas
mutual 
  Nf-iso1 : ∀{Γ α} → (t : SNf Γ α) → toSNf (toNf t) ≡ t
  Nf-iso1 (lam t) rewrite Nf-iso1 t = refl
  Nf-iso1 (neu (x , sp)) = cong neu (toSNe-$$ (var x) sp)

  toSNe-$$ : ∀{Γ α β} → (u : Ne Γ α) → (sp : Sp Γ α β)
    → toSNe (u $$ (toSt sp)) ≡ ((toSNe u) $$sp sp)
  toSNe-$$ u ∙ = sym ($$sp-z (toSNe u))
  toSNe-$$ u (s , sp) rewrite toSNe-$$ (app u (toNf s)) sp | Nf-iso1 s 
    = $$sp-comm (toSNe u) (s , ∙) sp

mutual
  Nf-iso2 : ∀{Γ α} → (t : Nf Γ α) → toNf (toSNf t) ≡ t
  Nf-iso2 (lam t) rewrite Nf-iso2 t = refl
  Nf-iso2 (↓ u) rewrite Ne-iso2 u = refl
 
  Ne-iso2 : ∀{Γ α} → (u : Ne Γ α) → toNe ((toSNe u)) ≡ u
  Ne-iso2 (var x) = refl
  Ne-iso2 (app u t) rewrite toNe-$$ (toSNe u) (toSNf t , ∙) | Ne-iso2 u | Nf-iso2 t = refl

  toNe-$$ : ∀{Γ α β} → (u : SNe Γ α) → (sp : Sp Γ α β) → toNe (u $$sp sp) ≡ (toNe u) $$ toSt sp
  toNe-$$ (x , xs) sp rewrite toSt-++ xs sp | $$-++-st (var x) (toSt xs) (toSt sp) = refl
  
  toSt-++ : ∀{Γ α β γ}(sp : Sp Γ α β)(sp' : Sp Γ β γ) → 
    toSt (sp Spine.++ sp') ≡ (toSt sp) Stack.++ (toSt sp')
  toSt-++ ∙ sp' = refl
  toSt-++ (s , sp) sp' rewrite toSt-++ sp sp' = refl

  $$-++-st : ∀{Γ α β γ}(u : Ne Γ α)(st : St Γ α β)(st' : St Γ β γ) → 
    u $$ (st Stack.++ st') ≡ (u $$ st) $$ st'
  $$-++-st u ∙ st' = refl
  $$-++-st u (s , st) st' rewrite $$-++-st (app u s) st st' = refl


-- Key lemma : the two normalization algorithms commute
-- Everything is quite sketchy, but it works

-- eta conversion
-- toNf commutes with napp


-- A bunch of commuting lemmas
renNe-$$ : ∀{Γ Δ α β}(u : Ne Γ α)(st : St Γ α β)(ρ : Ren Γ Δ) → 
  renNe (u $$ st) ρ ≡ (renNe u ρ) $$ (renSt st ρ)
renNe-$$ u ∙ ρ = refl
renNe-$$ u (s , st) ρ rewrite renNe-$$ (app u s) st ρ = refl

mutual
  toNf-ren : ∀{Γ Δ α}(t : SNf Γ α)(ρ : Ren Γ Δ) → 
    toNf (renSNf t ρ) ≡ renNf (toNf t) ρ
  toNf-ren (lam t) ρ rewrite toNf-ren t (ext ρ) = refl
  toNf-ren (neu (x , sp)) ρ rewrite toSt-ren sp ρ | renNe-$$ (var x) (toSt sp) ρ 
    = refl

  toSt-ren : ∀{Γ Δ α β}(sp : Sp Γ α β)(ρ : Ren Γ Δ) → 
   toSt (renSp sp ρ) ≡ renSt (toSt sp) ρ
  toSt-ren ∙ ρ = refl
  toSt-ren (s , sp) ρ = cong₂ _,_ (toNf-ren _ _) (toSt-ren _ _)

toSt-appSt : ∀{Γ α β γ}(sp : Sp Γ α (β ⇒ γ))(t : SNf Γ β) → 
  toSt (appSp sp t) ≡ appSt (toSt sp) (toNf t)
toSt-appSt ∙ t = refl
toSt-appSt (x , sp) t rewrite toSt-appSt sp t = refl

appSt-$$ : ∀{Γ α β γ}(u : Ne Γ α)(st : St Γ α (β ⇒ γ))(t : Nf Γ β) → 
  u $$ (appSt st t) ≡ app (u $$ st) t
appSt-$$ u ∙ t = refl
appSt-$$ u (s , st) t rewrite appSt-$$ (app u s) st t = refl

-- eva conversion
toNf-ne2nf : ∀{Γ α β}(x : Var Γ α)(sp : Sp Γ α β) → 
  toNf (Spine.ne2nf (x , sp)) ≡ Stack.ne2nf (toNe (x , sp))
toNf-ne2nf {α = α} {ι} x sp = refl
toNf-ne2nf {Γ} {α = α} {β ⇒ β'} x sp rewrite
    toNf-ne2nf (vs x) (appSp (wkSp sp) (nvar vz))
  = cong (lam ∘ Stack.ne2nf)
      -- (var vs x) $$ (toSt (appSt sp[vs] (nvar vz)))
      (trans (cong (λ z → var (vs x) $$ z) (toSt-appSt (wkSp sp) (nvar vz))) 
      -- (var vs x) $$ (appSt (toSt sp[w]) (ηvar vz))
      (trans (appSt-$$ (var (vs x)) (toSt (wkSp sp)) (toNf (nvar vz))) 
      -- app (var (vs x) $$ (toSt sp[vs])) (toNf (nvar vz))
      (cong₂ app 
        -- by toSt commutes with renaming
        (trans (cong (λ z → _ $$ z) (toSt-ren sp vs)) (sym (renNe-$$ (var x) (toSt sp) vs)))
        -- using I.H
        (toNf-ne2nf vz ∙))))


-- commuting napp
mutual 
  toNf-[] : ∀{Γ Δ α β}(s : SNf Γ α)(ρ : Ren Γ (Δ , β))(t : SNf Δ β) →
    toNf (s Spine.[ ρ , t ]) ≡ (toNf s) Stack.[ ρ , (toNf t) ]
  toNf-[] (lam s) ρ t = cong lam (trans (toNf-[] s _ _) (cong (λ z → (toNf s Stack.[ _ , z ])) (toNf-ren _ _)))
  toNf-[] (neu (x , sp)) ρ t with ρ x in p 
  ... | vz = 
    sym 
      (trans ($$-<> _ (toSt sp) _ _ _) 
      (trans (sym (<>Ne-vz {ρ = ρ} p)) 
      (trans (cong (λ z → (toNf t) Stack.$ z) (Stack.++-z {st = toSt sp [ ρ , toNf t ]St})) 
      (trans (cong (λ z → (toNf t) Stack.$ z) (sym (toSt-<> sp ρ t))) 
      (sym ((toNf-$ t (sp < ρ , t >))))))))
  ... | vs y = 
    sym 
    (trans (($$-<> _ (toSt sp) _ _ _)) 
    (trans (sym (<>Ne-vs {ρ = ρ} p)) 
    (cong (λ z → ↓ (var y $$ z)) (trans ((Stack.++-z {st = toSt sp [ ρ , toNf t ]St})) (sym (toSt-<> sp ρ t))))))

  toSt-<> : ∀{Γ Δ α β γ}(sp : Sp Γ α γ)(ρ : Ren Γ (Δ , β))(t : SNf Δ β) → 
    toSt (sp < ρ , t >) ≡ (toSt sp) [ ρ , toNf t ]St
  toSt-<> ∙ ρ t = refl
  toSt-<> (s , sp) ρ t = cong₂ _,_ (toNf-[] s ρ t) (toSt-<> sp ρ t)

  toNf-$ : ∀{Γ α β}(u : SNf Γ α)(sp : Sp Γ α β) → 
    toNf (u Spine.$ sp) ≡ (toNf u) Stack.$ (toSt sp)
  toNf-$ u ∙ = refl
  toNf-$ u (s , sp) rewrite toNf-$ (Spine.napp u s) sp | toNf-napp u s = refl

  toNf-napp : ∀{Γ α β}(s : SNf Γ (α ⇒ β))(t : SNf Γ α) → 
    toNf (Spine.napp s t) ≡ Stack.napp (toNf s) (toNf t)
  toNf-napp (lam s) t = toNf-[] s id t

-- Key lemma to soundness
snf-nf : ∀{Γ α}(t : Tm Γ α) → toNf (snf t) ≡ nf t
snf-nf (var x) rewrite toNf-ne2nf x ∙ rewrite toNf-ne2nf x ∙ = refl
snf-nf (lam t) rewrite snf-nf t = refl
snf-nf (app s t) rewrite toNf-napp (snf s) (snf t) | snf-nf s | snf-nf t = refl

nf-snf : ∀{Γ α}(t : Tm Γ α) → toSNf (nf t) ≡ snf t
nf-snf t = trans (cong toSNf (sym (snf-nf t))) (Nf-iso1 (snf t))

-- Soundness theorem
Soundness : ∀{Γ α}{t u : Tm Γ α} → t ≡t u → nf t ≡ nf u
Soundness {t = t} {u = u} p = 
  trans (sym (snf-nf t)) 
  (trans (cong toNf (soundness p)) (snf-nf u))

-------------------------------------

-- We can prove completeness directly
{- Embedding of normal forms into terms -}
mutual
  embNf : ∀{Γ σ} → Nf Γ σ → Tm Γ σ
  embNf (lam t) = lam (embNf t)
  embNf (↓ u) = embNe u

  embNe : ∀{Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (var x) = var x
  embNe (app t1 t2) = app (embNe t1) (embNf t2)

embSt : ∀{Γ σ τ} → St Γ σ τ → Tm Γ σ → Tm Γ τ
embSt ∙ acc = acc
embSt (t , sp) acc = embSt sp (app acc (embNf t))

-- congruence of terms for embSt
embSt-cong : ∀{Γ α β}{t u : Tm Γ α} → (sp : St Γ α β) → 
  t ≡t u → embSt sp t ≡t embSt sp u 
embSt-cong ∙ p = p
embSt-cong (x , sp) p = embSt-cong sp (p -$- idᵗ)


-- renamings commutes with embNf
mutual
  renNf-emb : ∀{Γ Δ α} → (t : Nf Γ α) → (ρ : Ren Γ Δ) → 
    embNf (renNf t ρ) ≡ ren (embNf t) ρ
  renNf-emb (lam t) ρ rewrite renNf-emb t (ext ρ) = refl
  renNf-emb (↓ t) ρ = renNe-emb t ρ

  renNe-emb : ∀{Γ Δ α} → (t : Ne Γ α) → (ρ : Ren Γ Δ) → 
    embNe (renNe t ρ) ≡ ren (embNe t) ρ
  renNe-emb (var x) ρ = refl
  renNe-emb (app t1 t2) ρ rewrite renNe-emb t1 ρ | renNf-emb t2 ρ = refl

renSt-emb : ∀{Γ Δ α β} → (sp : St Γ α β) → (t : Tm Γ α) → (ρ : Ren Γ Δ) → 
  embSt (renSt sp ρ) (ren t ρ) ≡ ren (embSt sp t) ρ
renSt-emb ∙ t ρ = refl
renSt-emb (s , sp) t ρ rewrite renNf-emb s ρ = trans refl (renSt-emb sp (app t (embNf s)) ρ)

mutual 
  -- η-expansion preserves equivalence
  ne2nf-comp : ∀{Γ α} → (u : Ne Γ α) → embNf (Stack.ne2nf u) ≡t embNe u 
  ne2nf-comp {α = ι} u = idᵗ
  ne2nf-comp {α = α ⇒ β} (var x) = 
    λt (
      (ne2nf-comp (app (wkNe (var x)) (ηvar vz))) 
      => (idᵗ -$- ηvar-comp vz)
    )
    => ≡η⁻¹
  ne2nf-comp {α = α ⇒ β} (app t1 t2) = 
    λt (ne2nf-comp (app (wkNe (app t1 t2)) (ηvar vz))) 
    => λt (Tm≡ (renNe-emb t1 vs) -$- (Tm≡ (renNf-emb t2 vs) )-$- ne2nf-comp (var vz)) 
    => ≡η⁻¹ 
    => Tm≡ refl

  ηvar-comp : ∀{Γ α} → (x : Var Γ α) → embNf (ηvar x) ≡t var x
  ηvar-comp x = ne2nf-comp (var x)

mutual
  []-comp : ∀{Γ Δ α β} → (t : Nf Γ α)→ (ρ : Ren Γ (Δ , β)) → (u : Nf Δ β) → 
    embNf (t Stack.[ ρ , u ]) ≡t ((embNf t) [ ρ , embNf u ]Tm)
  []-comp (lam t) ρ u = 
    λt (coerce (renNf-emb u vs) 
      ((λ z → embNf (t Stack.[ sw ∘ ext ρ , renNf u vs ]) ≡t ((embNf t) [ (sw ∘ ext ρ) , z ]Tm)))
       (([]-comp t (sw ∘ ext ρ) (wkNf u))))
  []-comp (↓ t) ρ u = <>-comp t ρ u ∙

  <>-comp : ∀{Γ Δ α β} → 
    (t : Ne Γ α) → (ρ : Ren Γ (Δ , β)) → 
    (u : Nf Δ β) → (sp : St Δ α ι) → 
    embNf (t < ρ , u > sp) ≡t embSt sp ((embNe t) [ ρ , (embNf u) ]Tm)
  <>-comp (var x) ρ u sp with ρ x
  ... | vz = $-comp u sp
  ... | vs y = $$-comp (var y) sp
  <>-comp (app t1 t2) ρ u sp = 
    <>-comp t1 ρ u ((t2 Stack.[ ρ , u ]) , sp) 
    => embSt-cong sp (idᵗ -$- []-comp t2 ρ u)

  $-comp : ∀{Γ α β} → (t : Nf Γ α) → (sp : St Γ α β) →
    embNf (t Stack.$ sp) ≡t embSt sp (embNf t) 
  $-comp t ∙ = idᵗ
  $-comp t (u , sp) = ($-comp (Stack.napp t u) sp) => (embSt-cong sp (napp-comp t u))

  $$-comp : ∀{Γ α β} → (t : Ne Γ α) → (sp : St Γ α β) →
    embNe (t $$ sp) ≡t embSt sp (embNe t)
  $$-comp t ∙ = idᵗ
  $$-comp t (u , sp) = $$-comp (app t u) sp

  napp-comp : ∀{Γ α β} → (s : Nf Γ (α ⇒ β)) → (t : Nf Γ α) → 
    embNf (Stack.napp s t) ≡t app (embNf s) (embNf t)
  napp-comp (lam s) t = ([]-comp s id t) => ≡β⁻¹

completeness : ∀{Γ α} → (t : Tm Γ α) → embNf (nf t) ≡t t
completeness (var x) = ηvar-comp x
completeness (lam t) = λt (completeness t)
completeness (app s t) = (napp-comp (nf s) (nf t)) => ((completeness s) -$- (completeness t))

-------------------------------------

-- Embedding commutes with isomorphism
mutual
  emb-toNf : ∀{Γ α}(t : SNf Γ α) → embSNf t ≡ embNf (toNf t)
  emb-toNf (lam t) rewrite emb-toNf t = refl
  emb-toNf (neu u) = emb-toNe u

  emb-toNe : ∀{Γ α}(u : SNe Γ α) → embSNe u ≡ embNe (toNe u)
  emb-toNe (x , sp) = emb-toSt sp (var x)

  emb-toSt : ∀{Γ α β}(sp : Sp Γ α β)(u : Ne Γ α) → 
    embSp sp (embNe u) ≡ embNe (u $$ (toSt sp))
  emb-toSt ∙ u = refl
  emb-toSt (s , sp) u rewrite emb-toNf s | emb-toSt sp (app u (toNf s)) = refl

emb-toSNf : ∀{Γ α}(t : Nf Γ α) → embNf t ≡ embSNf (toSNf t)
emb-toSNf t = trans (cong embNf (sym (Nf-iso2 t))) (sym (emb-toNf (toSNf t)))
-- embSNf o toSNf
-- = embNf o toNf o toSNf
-- = embNf

-- Normalization is idempotent on terms...
idem : ∀{Γ α}(t : Tm Γ α) → nf (embNf (nf t)) ≡ nf t
idem t = 
  -- (nf o embNf o nf) t
  trans (sym (snf-nf (embNf (nf t)))) 
  -- = (toNf o snf o embNf o nf) t
  (trans (cong (toNf ∘ snf) (emb-toSNf (nf t)))
  -- = (toNf o snf o embSNf o toSNf o nf) t
  (trans (cong (toNf ∘ snf ∘ embSNf) (nf-snf t))
  -- = (toNf o snf o embSNf o snf) t
  (trans (cong toNf (idemS t))
  -- = (toNf o snf) t
  (snf-nf t))))
  -- = nf t 

-- ... and normal forms, proof similar to above.
embNf-nf : ∀{Γ α}(t : Nf Γ α) → nf (embNf t) ≡ t
embNf-nf t = 
  trans (sym (snf-nf (embNf t))) 
  (trans (cong (toNf ∘ snf) (emb-toSNf t)) 
  ((trans (cong toNf (embSNf-nf (toSNf t))) (Nf-iso2 t))))

-- Hence, uniqueness of normal forms
unique : ∀{Γ α} → (t1 t2 : Nf Γ α) → embNf t1 ≡t embNf t2 → t1 ≡ t2
unique t1 t2 p = trans (sym (embNf-nf t1)) (trans (Soundness p) (embNf-nf t2))
 

  