{-# OPTIONS --prop --rewriting --type-in-type #-}

module Universes where

open import Lib
open import CwF

-- Universe of propositions, prerdered by implication
--------------------------------------------------------------------------------

Props : ∀ {Γ} → Ty Γ
Props {Γ} = ty
  (λ _ → Prop)
  (λ A B _ → A → B)
  (λ xx → xx)
  (λ f g xx → g (f xx))
  (λ _ A → A)
  (λ _ _ xx → xx)
  (λ f → f)

Props[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Props [ σ ]T ≡ Props
Props[] = refl

-- Interesting: in preorder TT, there is no embedding from Prop to Set!
-- The monotonicity of (Tm Γ Props) and (Tm Γ Sets) causes this extra weirdness.

ElP : ∀ {Γ} → Tm Γ Props → Ty Γ
ElP {Γ} t = ty
  (λ x → LiftP (! t x))
  (λ {x} xx yy f → 𝕋)
  _
  _
  (λ f xx → lift (R t f (lower xx)))
  _
  _

ElP[] : ∀ {Γ Δ t}{σ : Sub Γ Δ} → ElP t [ σ ]T ≡ ElP (t [ σ ]t)
ElP[] = refl

irrelevance : ∀ {Γ}{A : Tm Γ Props}(t u : Tm Γ (ElP A)) → t ≡ u
irrelevance t u = refl


-- Universe of sets, preordered by strict equality
--------------------------------------------------------------------------------

Sets : ∀ {Γ} → Ty Γ
Sets {Γ} = ty
  (λ _ → Set)
  (λ A B _ → A ≡ B)
  refl
  _◾_
  (λ _ A → A)
  (λ _ _ → refl)
  (λ p → p)

Sets[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Sets [ σ ]T ≡ Sets
Sets[] = refl

ElS : ∀ {Γ} → Tm Γ Sets → Ty Γ
ElS {Γ} t = ty
  (! t)
  (λ x y f → coe (R t f) x ≡ y)
  refl
  (λ { {x}{y}{z}{f}{g}{xx}{yy}{zz} refl refl → happly (coe-coe (R t f) (R t g)) xx})
  (λ f → coe (R t f))
  (λ _ _ → refl)
  λ { {x}{y}{z}{f}{g}{xx}{zz} refl → happly (coe-coe (R t f) (R t g)) xx ⁻¹}

ElS[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{t : Tm Δ Sets} → ElS t [ σ ]T ≡ ElS (t [ σ ]t)
ElS[] = refl

-- Universe of preorders, preordered by strict equality
--------------------------------------------------------------------------------

U : ∀ {Γ} → Ty Γ
U {Γ} = ty
  (λ _ → Con)
  (λ A B _ → A ≡ B)
  refl
  _◾_
  (λ _ A → A)
  (λ _ _ → refl)
  (λ p → p)

U[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → U [ σ ]T ≡ U
U[] = refl

ElU : ∀ {Γ} → Tm Γ U → Ty Γ
ElU {Γ} A = ty
  (λ x → ! (! A x))
  (λ {x}{y} Ax Ay f → R (! A y) (tr ! (R A f) Ax) Ay)
  (λ {x} → rfl (! A x))
  (λ {x}{y}{z}{f}{g}{xx}{yy}{zz} p q →
     trs (! A z) (
       trP (λ f → R (! A z) (f xx) (tr ! (R A g) yy)) (tr-tr ! (R A f) (R A g)⁻¹)
           (JP (λ !Az eq → R !Az (tr ! eq (tr ! (R A f) xx)) (tr ! eq yy))
               p (R A g)))
       q)
  (λ {x}{y} f xx → tr ! (R A f) xx)
  (λ {x}{y} f xx → rfl (! A y))
  (λ {x}{y}{z}{f}{g}{xx}{zz} p →
     trP (λ f → R (! A z) (f xx) zz) (tr-tr ! (R A f) (R A g)) p)

ElU[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{t : Tm Δ U} → ElU t [ σ ]T ≡ ElU (t [ σ ]t)
ElU[] = refl

-- Universe of preorders, preordered by preorder refinement
--------------------------------------------------------------------------------

UR : ∀ {Γ} → Ty Γ
UR {Γ} = ty
  (λ _ → Con)
  (λ A B _ → ΣPP (! A ≡ ! B) λ p → ∀ {x y} → R A x y → R B (coe p x) (coe p y))
  (λ {x}{xx} → refl , (λ p → p))
  (λ { {x}{y}{z}{f}{g}{xx}{yy}{zz} (p , p~) (q , q~) →
       (p ◾ q)
     , λ {x₁}{y₁} r → trP (λ f → R zz (f x₁) (f y₁)) (coe-coe p q ⁻¹) (q~ (p~ r)) })
  (λ _ A → A)
  (λ {x}{y} f A → refl , (λ p → p))
  (λ p → p)

UR[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → UR [ σ ]T ≡ UR
UR[] = refl

ElUR : ∀ {Γ} → Tm Γ UR → Ty Γ
ElUR {Γ} A = ty
  (λ x → ! (! A x))
  (λ {x}{y} Ax Ay f → R (! A y) (coe (₁ (R A f)) Ax) Ay)
  (λ {x} → rfl (! A x))
  (λ {x}{y}{z}{f}{g}{xx}{yy}{zz} p q →
     trs (! A z)
         (trP (λ f → R (! A z) (f xx) (coe (₁ (R A g)) yy))
              (coe-coe (₁ (R A f)) (₁ (R A g))⁻¹)
              (₂ (R A g) p))
         q)
  (λ {x}{y} f xx → coe (₁ (R A f)) xx)
  (λ {x}{y} f xx → rfl (! A y))
  (λ {x}{y}{z}{f}{g}{xx}{zz} p →
       trP (λ f → R (! A z) (f xx) zz) (coe-coe (₁ (R A f)) (₁ (R A g))) p)

ElUR[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{t : Tm Δ UR} → ElUR t [ σ ]T ≡ ElUR (t [ σ ]t)
ElUR[] = refl
