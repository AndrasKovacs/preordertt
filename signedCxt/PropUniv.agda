{-# OPTIONS --prop --rewriting --type-in-type #-}

module PropUniv where

open import Lib
open import CwF

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
-- The monotonicity of (Tm Γ Props) causes this extra weirdness.

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
