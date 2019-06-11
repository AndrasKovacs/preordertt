
{-# OPTIONS --prop --rewriting --type-in-type #-}

module Pi where

open import Lib
open import CwF

-- TODO: app, lam, etc.

-- contravariant Π
Π- : ∀ {Γ}(A : Ty (op Γ)) → Ty (Γ ▶- opT A) → Ty Γ
Π- {Γ} A B = ty
  (λ x → ΣSP ((xx : ! A x) → ! B (x , xx)) λ ff
         → ∀ {xx₀ xx₁ : ! A x}(xx₀₁ : R A xx₀ xx₁ (rfl Γ))
         → R B (ff xx₁) (ff xx₀) (rfl Γ , coeT-rec A (trs A xx₀₁ (cohT A (rfl Γ) xx₁))))
  (λ { {x₀}{x₁} (ff , ff~) (gg , gg~) x₀₁ →
      ∀ {xx₀ : ! A x₀}{xx₁ : ! A x₁}
      → (xx₁₀ : R A xx₁ xx₀ x₀₁) → R B (ff xx₀) (gg xx₁)
                                       (x₀₁ , coeT-rec A (trs A xx₁₀ (cohT A _ xx₀))) })

  (λ { {x} {ff , ff~}{xx₀}{xx₁} xx₁₀ → ff~ xx₁₀})
  (λ { {x₀}{x₁}{x₂} {x₀₁}{x₁₂} {ff , ff~}{gg , gg~}{hh , hh~} fg gh {xx₀}{xx₂} xx₂₀
      → trs B (fg {xx₀}{coeT A x₁₂ xx₂}(coeT-rec A xx₂₀)) (gh {coeT A x₁₂ xx₂}{xx₂}(cohT A x₁₂ xx₂))})
  (λ { {x₀}{x₁} x₀₁ (ff , ff~) →
         (λ xx₁ → coeT B (x₀₁ , (cohT A (rfl Γ) _)) (ff (coeT A x₀₁ xx₁)))
       , λ { {xx₁a}{xx₁b} xx₁ba →
           coeT-rec B (trs B (ff~ (coeT-rec A (trs A xx₁ba (cohT A _ _)))) (cohT B _ _))
           }})
  (λ { {x₀}{x₁} x₀₁ (ff , ff~) {xx₀}{xx₁} xx₁₀ →
        trs B (ff~ (coeT-rec A xx₁₀)) (cohT B _ _) })
  (λ { {x₀}{x₁}{x₂}{x₀₁}{x₁₂}{ff₀ , ff₀~}{ff₂ , ff₂~} ff₀₂ {xx₁}{xx₂} xx₂₁ →
       coeT-rec B (ff₀₂ (trs A xx₂₁ (cohT A _ _)))})

-- covariant Π (but we can still only use the domain type in contravariant positions!)
Π+ : ∀ {Γ}(A : Ty (op Γ)) → Ty (Γ ▶- A) → Ty Γ
Π+ {Γ} A B = ty
  (λ x → ΣSP ((xx : ! A x) → ! B (x , xx)) λ ff
         → ∀ {xx₀ xx₁ : ! A x}(xx₀₁ : R A xx₀ xx₁ (rfl Γ))
         → R B (ff xx₀) (ff xx₁) (rfl Γ , trs A xx₀₁ (cohT A _ _)))
  (λ { {x₀}{x₁} (ff , ff~) (gg , gg~) x₀₁
       → ∀ {xx₀ xx₁ : ! A x₁}(xx₀₁ : R A xx₀ xx₁ (rfl Γ))
       →  R B (ff (coeT A x₀₁ xx₀)) (gg xx₁) (x₀₁ , (coeT-rec A (trs A xx₀₁ (cohT A _ _))))
         })
  (λ { {x}{ff , ff~} {xx₀}{xx₁} xx₀₁ → ff~ (coeT-rec A xx₀₁)})
  (λ { {x₀}{x₁}{x₂} {x₀₁}{x₁₂} {ff , ff~}{gg , gg~}{hh , hh~} fg gh {xx₀}{xx₂} xx₀₂ →
        let fg~  = fg  (coeT-rec A (trs A xx₀₂ (cohT A _ _)))
            fg~' = ff~ (coeT-rec A (trs A (cohT A x₁₂ xx₀) (cohT A _ _)))
        in trs B fg~' (trs B fg~ (gh {xx₂}{xx₂} (rfl A)))
      })
  (λ { {x₀}{x₁} x₀₁ (ff , ff~) →
         (λ xx₁ → coeT B (x₀₁ , rfl A) (ff (coeT A x₀₁ xx₁)))
       , λ {xx₀}{xx₁} xx₀₁ →
           let p = ff~ {coeT A x₀₁ xx₀}{coeT A x₀₁ xx₁}
                       (coeT-rec A (trs A xx₀₁ (cohT A _ _)))
           in coeT-rec B (trs B p (cohT B _ _))})
  (λ { {x₀}{x₁} x₀₁ (ff , ff~) {xx₀}{xx₁} xx₀₁ →
       trs B (ff~ (coeT-rec A (trs A xx₀₁ (cohT A _ _)))) (cohT B _ _)})
  (λ { {x₀}{x₁}{x₂}{x₀₁}{x₁₂}{ff₀ , ff₀~}{ff₂ , ff₂~} ff₀₂ {xx₁}{xx₂} xx₂₁ →
       coeT-rec B (
         trs B (ff₀~ (coeT-rec A (coeT-rec A (cohT A _ _))))
               (ff₀₂ xx₂₁))})

-- opposite of covariant Π
Π+ᵒ : ∀ {Γ}(A : Ty (op Γ)) → Ty (Γ ▶- opT A) → Ty Γ
Π+ᵒ {Γ} A B = ty
  (λ x → ΣSP ((xx : ! A x) → ! B (x , xx)) λ ff →
         {xx₀ xx₁ : ! A x} (xx₀₁ : R A xx₀ xx₁ (rfl Γ)) →
         R B (ff xx₀)
             (coeT B (rfl Γ , coeT-rec A (trs A xx₀₁ (cohT A _ _))) (ff xx₁))
             (rfl Γ , rfl A))
  (λ { {x₀}{x₁} (ff , ff~) (gg , gg~) x₀₁ →
         {xx₀ xx₁ : ! A x₁} (xx₀₁ : R A xx₀ xx₁ (rfl Γ))
       → R B (coeT B (x₀₁ , coeT-rec A (trs A (cohT A x₀₁ xx₀) (cohT A _ _)))
                     (ff (coeT A x₀₁ xx₀)))
             (coeT B (rfl Γ , coeT-rec A (trs A xx₀₁ (cohT A _ _)))
                     (gg xx₁))
             (rfl Γ , coeT-rec A (cohT A (rfl Γ) xx₀))
             })
  (λ { {x}{ff , ff~} xx₀₁ → {!ff~ ?!}})
  {!!}
  {!!}
  {!!}
  {!!}
