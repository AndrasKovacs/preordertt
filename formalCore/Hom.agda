{-# OPTIONS --prop --rewriting --type-in-type #-}

module Hom where

open import Lib
open import CwF
open import Universes

-- Hom : ∀ {Γ Δ} → Sub Γ Δ → Sub Γ Δ → TyP Γ
-- Hom {Γ}{Δ} σ δ = tyP (λ x → R Δ (! σ x) (! δ x))

Hom : ∀ {Γ Δ} → Sub (op Γ) Δ → Sub Γ Δ → Tm Γ Props
Hom {Γ} {Δ} σ δ = tm
  (λ x → R Δ (! σ x) (! δ x))
  (λ {x}{y} f p → trs Δ (R σ f) (trs Δ p (R δ f)))

core : Con → Con
core Γ = con
  (! Γ)
  (λ x y → R Γ x y ∧ R Γ y x)
  (rfl Γ , rfl Γ)
  (λ {(f , f⁻¹)(g , g⁻¹) → trs Γ f g , trs Γ g⁻¹ f⁻¹})

core∙ : core ∙ ≡ ∙
core∙ = con≡ refl λ _ _ → propext _ λ _ → _ , _

coreT : ∀ {Γ} → Ty Γ → Ty Γ
coreT {Γ} A = ty
  (! A)
  (λ a b f → R A a b f ∧ R A b (coeT A f a) (rfl Γ))
  (λ {x}{xx} → (rfl A) , cohT A _ _)
  (λ { {x}{y}{z}{f}{g}{xx}{yy}{zz}(p , p⁻¹)(q , q⁻¹) →
       (trs A p q) ,
       (trs A {g = rfl Γ} q⁻¹ (coeT-rec A (trs A {g = g} p⁻¹
              (coeT-rec A (cohT A (trs Γ f g) xx)))))})
  (coeT A)
  (λ {x}{y} f xx → (cohT A f xx) , rfl A)
  (λ { {x}{y}{z}{f}{g}{a}{c} (p , p⁻¹) →
       (coeT-rec A p) ,
       trs A {g = rfl Γ} p⁻¹
           (coeT-rec A (trs A (cohT A f a) (cohT A g (coeT A f a))))})

core▶+ : ∀ {Γ A} → core (Γ ▶+ A) ≡ (core Γ ▶+ {!!})
core▶+ = {!!}

Rfl : ∀ {Γ Δ}(σ : Sub Γ Δ) → Tm Γ (ElP (Hom {!σ!} {!!}))
Rfl = {!!}

-- Rfl : ∀ {Γ Δ}(σ : Sub Γ (core Δ)) → Tm Γ (ElP (Hom (iS- Δ σ) (iS+ Δ σ)))
-- Rfl {Γ}{Δ} σ  = tm
--   (λ x → lift (rfl Δ))
--   _




-- -- foo : ∀ {Γ Δ} → Sub (op Γ) Δ → Sub Γ (op Δ)
-- -- foo {Γ}{Δ} σ = sub (! σ) (R σ)

-- -- foo⁻¹ : ∀ {Γ Δ} → Sub Γ (op Δ) → Sub (op Γ) Δ
-- -- foo⁻¹ {Γ}{Δ} σ = sub (! σ) (R σ)

-- -- fool : ∀ {Γ Δ}{σ} → foo⁻¹ (foo {Γ}{Δ} σ) ≡ σ
-- -- fool = refl

-- -- foor : ∀ {Γ Δ}{σ} → foo (foo⁻¹ {Γ}{Δ} σ) ≡ σ
-- -- foor = refl

-- -- bar : ∀ {Γ A} → Tm (op Γ) A → Tm Γ {!A!}
-- -- bar = {!!}

-- core : Con → Con
-- core Γ = con
--   (! Γ)
--   (λ x y → R Γ x y ∧ R Γ y x)
--   (rfl Γ , rfl Γ)
--   (λ {(f , f⁻¹)(g , g⁻¹) → trs Γ f g , trs Γ g⁻¹ f⁻¹})

-- iS+ : ∀ {Γ} Δ → Sub Γ (core Δ) → Sub Γ Δ
-- iS+ {Γ} Δ σ = sub (! σ) (λ f → ₁ (R σ f))

-- iS- : ∀ {Γ} Δ → Sub Γ (core Δ) → Sub Γ (op Δ)
-- iS- {Γ} Δ σ = sub (! σ) (λ f → ₂ (R σ f))

-- Hom : ∀ {Γ Δ} → Sub Γ (op Δ) → Sub Γ Δ → Tm Γ Props
-- Hom {Γ} {Δ} σ δ = tm
--   (λ x → R Δ (! σ x) (! δ x))
--   (λ {x}{y} f p → trs Δ (R σ f) (trs Δ p (R δ f)))

-- Hom[] : ∀ {Γ Σ Δ}{ν : Sub Γ Σ}{σ : Sub Σ (op Δ)}{δ : Sub Σ Δ}
--         → Hom σ δ [ ν ]t ≡ Hom (σ ∘ ν) (δ ∘ ν)
-- Hom[] = refl

-- -- no substitution rules needed for Rfl, Trs, because of proof irrelevance
-- Rfl : ∀ {Γ Δ}(σ : Sub Γ (core Δ)) → Tm Γ (ElP (Hom (iS- Δ σ) (iS+ Δ σ)))
-- Rfl {Γ}{Δ} σ  = tm
--   (λ x → lift (rfl Δ))
--   _

-- Trs :
--   ∀ {Γ Δ}{σ₀ : Sub Γ (op Δ)}{σ₁ : Sub Γ (core Δ)}{σ₂ : Sub Γ Δ}
--   → Tm Γ (ElP (Hom σ₀ (iS+ Δ σ₁)))
--   → Tm Γ (ElP (Hom (iS- Δ σ₁) σ₂))
--   → Tm Γ (ElP (Hom σ₀ σ₂))
-- Trs {Γ} {Δ} {σ₀} {σ₁} {σ₂} σ₀₁ σ₁₂ = tm
--   (λ x → lift (trs Δ (lower (! σ₀₁ x)) (lower (! σ₁₂ x))))
--   _

-- --------------------------------------------------------------------------------

-- opT : ∀ {Γ} → Ty Γ → Ty Γ
-- opT {Γ} A = ty
--   (λ x → ! A x)
--   (λ a b f → R A b (coeT A f a) (rfl Γ))
--   (λ {x}{a} → cohT A (rfl Γ) a)
--   (λ {x}{y}{z}{f}{g}{a}{b}{c} ff gg →
--      trs A {g = rfl Γ} gg (coeT-rec A (trs A {g = g}
--          ff (coeT-rec A (cohT A (trs Γ f g) a)))))
--   (coeT A)
--   (λ f a → coeT-rec A (cohT A f a))
--   (λ {x}{y}{z}{f}{g}{a}{c} ff →
--      trs A {g = rfl Γ} ff
--      (coeT-rec A (trs A (cohT A f a) (cohT A g (coeT A f a)))))

-- coreT : ∀ {Γ} → Ty Γ → Ty Γ
-- coreT {Γ} A = ty
--   (! A)
--   (λ a b f → R A a b f ∧ R A b (coeT A f a) (rfl Γ))
--   (λ {x}{xx} → (rfl A) , cohT A _ _)
--   (λ { {x}{y}{z}{f}{g}{xx}{yy}{zz}(p , p⁻¹)(q , q⁻¹) →
--        (trs A p q) ,
--        (trs A {g = rfl Γ} q⁻¹ (coeT-rec A (trs A {g = g} p⁻¹
--               (coeT-rec A (cohT A (trs Γ f g) xx)))))})
--   (coeT A)
--   (λ {x}{y} f xx → (cohT A f xx) , rfl A)
--   (λ { {x}{y}{z}{f}{g}{a}{c} (p , p⁻¹) →
--        (coeT-rec A p) ,
--        trs A {g = rfl Γ} p⁻¹
--            (coeT-rec A (trs A (cohT A f a) (cohT A g (coeT A f a))))})

-- -- HomT : ∀ {Γ Δ A σ₀ σ₁}
-- --   → Tm Γ (ElP (Hom {Γ}{Δ} σ₀ σ₁))
-- --   → Tm (op Γ) (A [ opS σ₀ ]T)
-- --   → Tm Γ (A [ σ₁ ]T)
-- --   → Tm Γ Props
-- -- HomT {Γ} {Δ} {A} {σ₀} {σ₁} σ₀₁ t₀ t₁ = tm
-- --   (λ x → R A (! t₀ x) (! t₁ x) (lower (! σ₀₁ x)))
-- --   (λ f p → trs A (R t₀ f) (trs A p (R t₁ f)))

-- -- i+ : ∀ {Γ} A → Tm Γ (coreT A) → Tm Γ A
-- -- i+ {Γ} A t = tm (! t) (λ f → ₁ (R t f))

-- -- i- : ∀ {Γ} A → Tm Γ (coreT A) → Tm Γ (opT A)
-- -- i- A t = tm (! t) λ f → ₂ (R t f)

-- -- uncore : ∀ {Γ} → Sub (core Γ) Γ
-- -- uncore {Γ} = sub (λ z → z) ₁

-- -- RflT : ∀ {Γ A}(t : Tm Γ (coreT A))
-- --      → Tm Γ (ElP (HomT {{!!}}{{!!}}{{!!}}{{!Rfl!}}{{!!}}{!!} {!!} {!!}))
-- -- RflT = {!!}



-- HomT :
--   ∀ {Γ A} → Tm Γ (opT A) → Tm Γ A → Tm Γ Props
-- HomT {Γ} {A} t u = tm
--   (λ x → R A (! t x) (! u x) (rfl Γ))
--   (λ {x}{y} f p → trs A {g = rfl Γ} (R t f) (coeT-rec A (trs A p (R u f))))

-- i+ : ∀ {Γ} A → Tm Γ (coreT A) → Tm Γ A
-- i+ {Γ} A t = tm (! t) (λ f → ₁ (R t f))

-- i- : ∀ {Γ} A → Tm Γ (coreT A) → Tm Γ (opT A)
-- i- A t = tm (! t) λ f → ₂ (R t f)

-- ReflT :
--   ∀ {Γ A}(t : Tm Γ (coreT A)) → Tm Γ (ElP (HomT (i- A t) (i+ A t)))
-- ReflT {Γ} {A} t = tm (λ x → lift (rfl A)) _

-- TrsT :
--   ∀ {Γ A}{t : Tm Γ (opT A)}{u : Tm Γ (coreT A)}{v : Tm Γ A}
--   → Tm Γ (ElP (HomT t (i+ A u)))
--   → Tm Γ (ElP (HomT (i- A u) v))
--   → Tm Γ (ElP (HomT t v))
-- TrsT {Γ} {A} {t} {u} {v} p q = tm
--   (λ x → lift (trs A (lower (! p x)) (lower (! q x))))
--   _

-- open import Pi

-- refl2 : ∀ {A : Ty ∙}
--    → Tm ∙ (Π (coreT A)
--         (ElP (HomT {(∙ ▶- coreT A)}{A [ p- (coreT A) ]T}
--              {!!}
--              {!!})))  -- already fails because we can't get a (coreT A)
--                       -- variable from the negative context position
-- refl2 {A} = {!!}
