{-# OPTIONS --prop --rewriting --type-in-type #-}

module Pi where

open import Lib
open import CwF

Π : ∀ {Γ}(A : Ty (op Γ)) → Ty (Γ ▶- A) → Ty Γ
Π {Γ} A B = ty
  (λ x → ΣSP ((xx : ! A x) → ! B (x , xx)) λ f
         → ∀ {xx₀ xx₁}(xx₁₀ : R A xx₁ xx₀ (rfl Γ)) → R B (f xx₀) (f xx₁) (rfl Γ , xx₁₀))

  (λ { {x₀}{x₁} (f , pf) (g , pg) x₀₁ →
     ∀ {xx₀ xx₁}(xx₁₀ : R A xx₁ xx₀ x₀₁) → R B (f xx₀) (g xx₁) (x₀₁ , xx₁₀) })

  (λ { {x}{f , pf} {xx₀}{xx₁} xx₁₀ → pf xx₁₀ })

  (λ { {x₀}{x₁}{x₂} {x₀₁}{x₁₂} {f , f~}{g , g~}{h , h~} fg gh {xx₀}{xx₂} xx₂₀ →
       trs B (fg (coeT-rec A xx₂₀)) (gh (cohT A x₁₂ xx₂))})

  (λ { {x₀}{x₁} x₀₁ (f , f~) →
       (λ xx₁ → coeT B (x₀₁ , cohT A x₀₁ xx₁) (f (coeT A x₀₁ xx₁)))
              , λ { {xx₁a}{xx₁b} xx₁ba →
                 let fab = f~ (coeT-rec A {f = x₀₁}{rfl Γ} {xx₁b}{coeT A x₀₁ xx₁a}
                                          (trs A xx₁ba (cohT A x₀₁ xx₁a)))
                 in coeT-rec B (trs B fab (cohT B (x₀₁ , cohT A x₀₁ xx₁b) _))
              }})

  (λ { {x₀}{x₁} x₀₁ (f , f~) {xx₀}{xx₁} xx₁₀ →
       trs B (f~ (coeT-rec A xx₁₀))
             (cohT B (x₀₁ , cohT A x₀₁ xx₁) (f (coeT A x₀₁ xx₁)))})

  (λ { {x₀}{x₁}{x₂}{x₀₁}{x₁₂}{ff₀ , ff₀~}{ff₂ , ff₂~} ff₀₂ {xx₁}{xx₂} xx₂₁ →
      coeT-rec B (ff₀₂ (trs A xx₂₁ (cohT A x₀₁ xx₁)))})

Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}(A : Ty (op Δ))(B : Ty (Δ ▶- A))
      → Π A B [ σ ]T ≡ Π (A [ opS σ ]T) (B [ _^-_ {Γ}{Δ} (opS σ) A ]T)
Π[] {Γ} {Δ} {σ} A B = refl

app : ∀ {Γ}{A : Ty (op Γ)}{B : Ty (Γ ▶- A)} → Tm Γ (Π A B) → Tm (Γ ▶- A) B
app {Γ} {A} {B} t =
  tm (λ {(γ , a) → ₁ (! t γ) a}) (λ {(γ₀₁ , a₁₀) → R t γ₀₁ a₁₀})

lam : ∀ {Γ}{A : Ty (op Γ)}{B : Ty (Γ ▶- A)} → Tm (Γ ▶- A) B → Tm Γ (Π A B)
lam {Γ} {A} {B} t =
  tm (λ γ → (λ a → ! t (γ , a)) , λ a₁₀ → R t (rfl Γ , a₁₀))
       (λ γ₀₁ a₁₀ → R t (γ₀₁ , a₁₀))

Πβ :  ∀ {Γ}{A : Ty (op Γ)}{B : Ty (Γ ▶- A)}(t : Tm (Γ ▶- A) B)
      → app {Γ}{A}{B} (lam {Γ}{A}{B} t) ≡ t
Πβ {Γ} {A} {B} t = refl

Πη : ∀ {Γ}{A : Ty (op Γ)}{B : Ty (Γ ▶- A)}
       (t : Tm Γ (Π A B)) → lam {Γ}{A}{B} (app {Γ}{A}{B} t) ≡ t
Πη {Γ} {A} {B} t = refl

app[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Ty (op Δ)}{B : Ty (Δ ▶- A)}(t : Tm Δ (Π A B))
        → app {Δ}{A}{B} t [ _^-_ {Γ}{Δ} (opS σ) A ]t
        ≡ app {Γ}{A [ opS σ ]T}{B [ _^-_ {Γ}{Δ} (opS σ) A ]T}
              (t [ σ ]t)
app[] {Γ} {Δ} {σ} {A} {B} t = refl
