{-# OPTIONS --prop --rewriting --type-in-type #-}

{-
Category-with-families structure for preorders. Supports extra structure
for contravariant context extensions and taking opposite preorders.
-}

module CwF where

open import Lib

infixr 6 _∘_
infixl 8 _[_]t
infixl 7 _[_]T
infixl 4 _▶+_ _▶-_ -- _▶≈_

record Con : Set where
  constructor con
  field
    !   : Set
    R   : ! → ! → Prop
    rfl : ∀ {x} → R x x
    trs : ∀ {x y z} → R x y → R y z → R x z
open Con public

abstract
  con≡ :
    ∀ {Γ Δ : Con}
    → (p : ! Γ ≡ ! Δ)
    → (∀ x y → R Γ x y ≡ R Δ (coe p x) (coe p y))
    → Γ ≡ Δ
  con≡ refl q with funext λ x → funext λ y → q x y
  ... | refl = refl

op : Con → Con
op Γ = con
  (! Γ)
  (λ x y → R Γ y x)
  (rfl Γ)
  (λ p q → trs Γ q p)

op-inv : ∀ {Γ} → op (op Γ) ≡ Γ
op-inv = refl

core : Con → Con
core Γ = con
  (! Γ)
  (λ x y → R Γ x y ∧ R Γ y x)
  (rfl Γ , rfl Γ)
  (λ {(f , f⁻¹)(g , g⁻¹) → trs Γ f g , trs Γ g⁻¹ f⁻¹})

-- preorder opfibrations (non-split here, but syntax should probably support
--   split opfib, for extra computation)
record Ty (Γ : Con) : Set where
  constructor ty
  private module Γ = Con Γ
  field
    !   : ! Γ → Set
    R   : ∀ {x y} → ! x → ! y → R Γ x y → Prop
    rfl : ∀ {x xx} → R xx xx (rfl Γ {x})
    trs : ∀ {x y z f g xx yy zz} → R {x}{y} xx yy f → R {y}{z} yy zz g
                                 → R  xx zz (trs Γ f g)
    coeT : ∀ {x y} → Γ.R x y → ! x → ! y
    cohT : ∀ {x y}(f : Γ.R x y)(xx : ! x) → R xx (coeT f xx) f
    coeT-rec : ∀ {x y z}{f : Γ.R x y}{g : Γ.R y z}{xx zz} → R xx zz (Γ.trs f g)
              → R (coeT f xx) zz g
open Ty public

abstract
  ty≡ : ∀ {Γ}{A B : Ty Γ}
    → (p : (x : ! Γ) → ! A x ≡ ! B x)
    → (∀ {x y : ! Γ} (a : ! A x) (b : ! A y) f → R A a b f ≡ R B (coe (p x) a) (coe (p y) b) f)
    → (∀ {x y}(f : R Γ x y) (a : ! A x) → coe (p y) (coeT A f a) ≡ coeT B f (coe (p x) a))
    → A ≡ B
  ty≡ {Γ} {A} {B} p q r with funext p
  ... | refl with ((λ {x}{y} → R A {x}{y}) ≡ R B) ∋P
         funexti λ x → funexti λ y → funext λ a → funext λ b → funextP λ f → q a b f
  ... | refl with ((λ {x}{y} → coeT A {x}{y}) ≡ coeT B) ∋P
         funexti λ x → funexti λ y → funextP λ f → funext (λ a → r f a)
  ... | refl = refl

opT : ∀ {Γ} → Ty Γ → Ty Γ
opT {Γ} A = ty
  (λ x → ! A x)
  (λ a b f → R A b (coeT A f a) (rfl Γ))
  (λ {x}{a} → cohT A (rfl Γ) a)
  (λ {x}{y}{z}{f}{g}{a}{b}{c} ff gg →
     trs A {g = rfl Γ} gg (coeT-rec A (trs A {g = g}
         ff (coeT-rec A (cohT A (trs Γ f g) a)))))
  (coeT A)
  (λ f a → coeT-rec A (cohT A f a))
  (λ {x}{y}{z}{f}{g}{a}{c} ff →
     trs A {g = rfl Γ} ff
     (coeT-rec A (trs A (cohT A f a) (cohT A g (coeT A f a)))))

opT-inv : ∀ {Γ A} → opT (opT {Γ} A) ≡ A
opT-inv {Γ} {A} = ty≡
  (λ _ → refl)
  (λ {x}{y} a b f → propext
    (λ p → trs A (cohT A f a) (trs A {g = rfl Γ} p (coeT-rec A (rfl A))) )
    (λ p → coeT-rec A (trs A p (cohT A _ _))))
  (λ _ _ → refl)

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

record Sub (Γ Δ : Con) : Set where
  constructor sub
  field
    ! : ! Γ → ! Δ
    R : ∀ {x y} → R Γ x y → R Δ (! x) (! y)
open Sub public

sub≡ : ∀ {Γ Δ}{σ δ : Sub Γ Δ} → (∀ x → ! σ x ≡ ! δ x) → σ ≡ δ
sub≡ {Γ} {Δ} {σ} {δ} p with funext p
... | refl = refl

opS : ∀ {Γ Δ} → Sub Γ Δ → Sub (op Γ) (op Δ)
opS {Γ}{Δ} σ = sub
  (! σ)
  (λ { {x₀}{x₁} → R σ {x₁}{x₀}})

opS-inv : ∀ {Γ Δ}{σ : Sub Γ Δ} → opS (opS σ) ≡ σ
opS-inv = refl

iS+ : ∀ {Γ} Δ → Sub Γ (core Δ) → Sub Γ Δ
iS+ {Γ} Δ σ = sub (! σ) (λ f → ₁ (R σ f))

iS- : ∀ {Γ} Δ → Sub Γ (core Δ) → Sub Γ (op Δ)
iS- {Γ} Δ σ = sub (! σ) (λ f → ₂ (R σ f))

record Tm (Γ : Con) (A : Ty Γ) : Set where
  constructor tm
  field
    ! : (x : ! Γ) → ! A x
    R : ∀ {x y}(f : R Γ x y) → R A (! x) (! y) f
open Tm public

abstract
  tm≡ : ∀ {Γ A}{t u : Tm Γ A}
      → (∀ x → ! t x ≡ ! u x)
      → t ≡ u
  tm≡ {Γ} {A} {t} {u} p with funext p
  ... | refl = refl

∙ : Con
∙ = con ⊤ (λ _ _ → 𝕋) _ _

op∙ : op ∙ ≡ ∙
op∙ = refl

_▶+_ : (Γ : Con) → Ty Γ → Con
Γ ▶+ A = con
  (Σ (! Γ) (! A))
  (λ {(γ₀ , a₀) (γ₁ , a₁) → ΣPP (R Γ γ₀ γ₁) (R A a₀ a₁)})
  (rfl Γ , rfl A)
  (λ p q → (trs Γ (₁ p) (₁ q)) , trs A (₂ p) (₂ q))

_▶-_ : (Γ : Con) → Ty (op Γ) → Con
Γ ▶- A  = con
  (Σ (! Γ) (! A))
  (λ {(x , a)(y , b) → ΣPP (R Γ x y) (λ f → R A a (coeT A f b) (rfl Γ))})
  (λ { {x , a} → (rfl Γ) , cohT A _ _})
  (λ { {x , a}{y , b}{z , c}(f , f')(g , g') →
       (trs Γ f g) , trs A {g = rfl Γ} f' (coeT-rec A (trs A {g = f} g'
                     (coeT-rec A (cohT A _ _))))})

op▶+ : ∀ {Γ A} → op (Γ ▶+ A) ≡ (op Γ ▶- opT A)
op▶+ {Γ} {A} = con≡
  refl
  (λ {(x , a)(y , b) → propext
    (λ {(p , q) → p , coeT-rec A (trs A q (cohT A _ _))})
    (λ {(p , q) → p , (trs A (cohT A p b) (trs A {g = rfl Γ} q (coeT-rec A (rfl A))))})})

op▶- : ∀ {Γ A} → op (Γ ▶- A) ≡ (op Γ ▶+ opT A)
op▶- {Γ} {A} = refl

-- _▶≈_ : (Γ : Con) → Ty (core Γ) → Con
-- Γ ▶≈ A = con
--   (Σ (! Γ) (! A))
--   (λ {(x , a)(y , b) → ΣPP (R Γ x y) λ f → ΣPP (R Γ y x) λ g → R A a b (f , g)})
--   (rfl Γ , rfl Γ , rfl A)
--   (λ { {x}{y}{z} (f , g , h)(f' , g' , h')
--       → (trs Γ f f') , trs Γ g' g , trs A h h'})

_[_]T : ∀ {Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
_[_]T {Γ} {Δ} A σ =
  ty (λ γ → ! A (! σ γ))
     (λ γ₀ γ₁ γ₀₁ → R A γ₀ γ₁ (R σ γ₀₁))
     (rfl A)
     (trs A)
     (λ p → coeT A (R σ p))
     (λ p → cohT A (R σ p))
     (coeT-rec A)

id : ∀ {Γ} → Sub Γ Γ
id = sub (λ x → x) (λ p → p)

op-id : ∀ {Γ} → opS (id {Γ}) ≡ id
op-id = refl

_∘_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
σ ∘ δ = sub (λ x → ! σ (! δ x)) (λ p → R σ (R δ p))

op∘ : ∀ {Γ Δ Σ}(σ : Sub Δ Σ)(δ : Sub Γ Δ) → opS (σ ∘ δ) ≡ opS σ ∘ opS δ
op∘ σ δ = refl

idl : {Γ Δ : Con} {σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : {Γ Δ : Con} {σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

ass   : {Γ Δ : Con} {Σ : Con} {Ω : Con} {σ : Sub Σ Ω} {δ : Sub Δ Σ}
        {ν : Sub Γ Δ} → ((σ ∘ δ) ∘ ν) ≡ (σ ∘ (δ ∘ ν))
ass = refl

[id]T : ∀ {Γ}{A : Ty Γ} → A [ id ]T ≡ A
[id]T = refl

[∘]T : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {σ : Sub Γ Δ}
       {δ : Sub Δ Σ} → A [ δ ]T [ σ ]T ≡ A [ δ ∘ σ ]T
[∘]T = refl

_[_]t : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ]t = tm (λ γ → ! t (! σ γ)) (λ p → R t (R σ p))

[id]t : ∀ {Γ}{A : Ty Γ}{t : Tm Γ A} → t [ id ]t ≡ t
[id]t = refl

[∘]t : {Γ Δ : Con} {Σ : Con} {A : Ty Σ} {σ : Sub Γ Δ}{δ : Sub Δ Σ}{t : Tm Σ A}
       → t [ δ ]t [ σ ]t ≡ t [ δ ∘ σ ]t
[∘]t = refl

ε  : ∀{Γ} → Sub Γ ∙
ε = _

opε : ∀ {Γ} → opS (ε{Γ}) ≡ ε
opε = refl

,+ : ∀{Γ Δ} A (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶+ A)
,+ A σ t = sub (λ x → (! σ x) , (! t x))
               (λ {x}{y} f → (R σ f) , (R t f))

,- : ∀{Γ Δ} A (σ : Sub Γ Δ) → Tm (op Γ) (opT A [ opS σ ]T) → Sub Γ (Δ ▶- A)
,- {Γ} {Δ} A σ t = sub
  (λ x → (! σ x) , (! t x))
  (λ f → (R σ f) , R t f)

op,+ : ∀{Γ Δ} A (σ : Sub Γ Δ)(t : Tm Γ (A [ σ ]T)) →
    coe (Sub (op Γ) & op▶+ {Δ}{A}) (opS (,+ A σ t))
  ≡ ,- (opT A) (opS σ)
       (coe ((λ A → Tm Γ (A [ σ ]T)) & (opT-inv {Δ}{A} ⁻¹) ) t)
op,+ {Γ}{Δ} A σ t = cheatP -- OK

op,- : ∀{Γ Δ} A (σ : Sub Γ Δ)(t : Tm (op Γ) (opT A [ opS σ ]T))
       → opS (,- A σ t) ≡ ,+ {op Γ}{op Δ} (opT A) (opS σ) t
op,- A σ t = refl

p+ : ∀ {Γ} A → Sub (Γ ▶+ A) Γ
p+ {Γ} A = sub ₁ ₁

p+∘ : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → p+ A ∘ (,+ A σ t) ≡ σ
p+∘ = refl

p- : ∀ {Γ} A → Sub (Γ ▶- A) Γ
p- A = sub ₁ ₁

p-∘ : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → p- A ∘ ,- A σ t ≡ σ
p-∘ = refl

op-p+ : ∀ {Γ A} →
     coe ((λ x → Sub x (op Γ)) & op▶+ {Γ}{A})
     (opS (p+ {Γ} A))
   ≡ p- {op Γ} (opT A)
op-p+ {Γ} {A} = cheatP -- OK

q+ : ∀ {Γ} A → Tm (Γ ▶+ A) (A [ p+ A ]T)
q+ {Γ} A = tm ₂ ₂

q+[] : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → q+ A [ ,+ A σ t ]t ≡ t
q+[] = refl

-- Harper & Licata in 2D directed TT: there is no rule for using contravariant variables!
-- It seems that it can't even be given in the model.

-- We can only refer to negative variables if we flip the context (by being in a negative
-- position).

-- q- : ∀ {Γ A} → Tm (Γ ▶- coreT A) (A [ {!p- {Γ} A!} ]T)
-- q- {Γ}{A} = {!!}

,+η : ∀ {Γ Δ A}{σ : Sub Γ (Δ ▶+ A)} → σ ≡ ,+ A (p+ A ∘ σ) (q+ A [ σ ]t)
,+η = refl

,+∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]T)}{δ : Sub Σ Δ}
      → ,+ A σ t ∘ δ ≡ ,+ A (σ ∘ δ) (t [ δ ]t)
,+∘ = refl

,-∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ Γ}{t : Tm (op Δ) (opT A [ opS σ ]T)}{δ : Sub Σ Δ}
      → ,- A σ t ∘ δ ≡ ,- A (σ ∘ δ) (t [ opS δ ]t)
,-∘ = refl

_^+_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶+ (A [ σ ]T)) (Δ ▶+ A)
_^+_ σ A = sub (λ γ → ! σ (₁ γ) , ₂ γ) (λ p → R σ (₁ p) , ₂ p)
infixl 5 _^+_

_^-_ : ∀ {Γ Δ : Con}(σ : Sub (op Γ) (op Δ))(A : Ty (op Δ)) → Sub (Γ ▶- (A [ σ ]T)) (Δ ▶- A)
_^-_ {Γ} {Δ} σ A = sub (λ {(p , q) → ! σ p , q}) (λ {(p , q) → R σ p , q})
infixl 5 _^-_
