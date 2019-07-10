{-# OPTIONS --prop --rewriting --type-in-type #-}

module CwF where

open import Lib
import Lib

infixr 6 _∘_
infixl 8 _[_]t
infixl 7 _[_]T
infixl 4 _▶+_ _▶-_

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

Con-inv : ∀ {Γ} → op (op Γ) ≡ Γ
Con-inv = refl

-- preorder opfibrations (non-split here, but should be split in syntax)
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

record TyP (Γ : Con) : Set where
  constructor ty
  private module Γ = Con Γ
  field
    !   : ! Γ → Prop
    R   : ∀ {x y} → ! x → ! y → R Γ x y → Prop
    rfl : ∀ {x xx} → R xx xx (rfl Γ {x})
    trs : ∀ {x y z f g xx yy zz} → R {x}{y} xx yy f → R {y}{z} yy zz g
                                 → R  xx zz (trs Γ f g)
    coeT : ∀ {x y} → Γ.R x y → ! x → ! y
    cohT : ∀ {x y}(f : Γ.R x y)(xx : ! x) → R xx (coeT f xx) f
    coeT-rec : ∀ {x y z}{f : Γ.R x y}{g : Γ.R y z}{xx zz} → R xx zz (Γ.trs f g)
              → R (coeT f xx) zz g
open TyP public

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

record Sub (Γ Δ : Con) : Set where
  constructor sub
  field
    ! : ! Γ → ! Δ
    R : ∀ {x y} → R Γ x y → R Δ (! x) (! y)
open Sub public

sub≡ : ∀ {Γ Δ}{σ δ : Sub Γ Δ} → (∀ x → ! σ x ≡ ! δ x) → σ ≡ δ
sub≡ {Γ} {Δ} {σ} {δ} p with funext p
... | refl = refl

sub≃ : ∀ {Γ Γ' Δ Δ'}{σ : Sub Γ Δ}{δ : Sub Γ' Δ'}
       → (Γ ≡ Γ')
       → (Δ ≡ Δ')
       → (∀ {x₀}{x₁} (x₀₁ : x₀ ≃ x₁) → ! σ x₀ ≃ ! δ x₁) → σ ≃ δ
sub≃ {Γ} {.Γ} {Δ} {.Δ} {σ} {δ} refl refl r = sub≡ (λ x → uñ (r refl̃)) ~

opS : ∀ {Γ Δ} → Sub Γ Δ → Sub (op Γ) (op Δ)
opS {Γ}{Δ} σ = sub
  (! σ)
  (λ { {x₀}{x₁} → R σ {x₁}{x₀}})

Sub-inv : ∀ {Γ Δ}{σ : Sub Γ Δ} → opS (opS σ) ≡ σ
Sub-inv = refl

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

-- record TmP (Γ : Con) (A : TyP Γ) : Prop where
--   constructor tmP
--   field
--     ! : (x : ! Γ) → ! A x
-- open TmP public

∙ : Con
∙ = con ⊤ (λ _ _ → 𝕋) _ _

op∙ : op ∙ ≡ ∙
op∙ = refl

_▶+_ : (Γ : Con) → Ty Γ → Con
Γ ▶+ A =
  con
    (Σ (! Γ) (! A))
    (λ {(γ₀ , a₀) (γ₁ , a₁) → ΣPP (R Γ γ₀ γ₁) (R A a₀ a₁)})
    (rfl Γ , rfl A)
    (λ p q → (trs Γ (₁ p) (₁ q)) , trs A (₂ p) (₂ q))

_▶-_ : (Γ : Con) → Ty (op Γ) → Con
Γ ▶- A  = con
  (Σ (! Γ) (! A))
  (λ {(x , xx)(y , yy) → ΣPP (R Γ x y) (R A yy xx)})
  (rfl Γ , rfl A)
  (λ {(p , p')(q , q') → trs Γ p q , trs A q' p'})

op▶+ : ∀ {Γ A} → op (Γ ▶+ A) ≡ (op Γ ▶- A)
op▶+ = refl

op▶- : ∀ {Γ A} → op (Γ ▶- A) ≡ (op Γ ▶+ A)
op▶- = refl

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
,+ A σ t = sub (λ x → ! σ x , ! t x) (λ p → R σ p , R t p)

,- : ∀{Γ Δ} A (σ : Sub Γ Δ) → Tm (op Γ) (A [ opS σ ]T) → Sub Γ (Δ ▶- A)
,- A σ t = sub (λ x → ! σ x , ! t x) (λ p → R σ p , R t p)

op,+ : ∀{Γ Δ} A (σ : Sub Γ Δ)(t : Tm Γ (A [ σ ]T)) → opS (,+ A σ t) ≡ ,- A (opS σ) t
op,+ A σ t = refl

op,- : ∀{Γ Δ} A (σ : Sub Γ Δ)(t : Tm (op Γ) (A [ opS σ ]T))
       → opS (,- A σ t) ≡ ,+ A (opS σ) t
op,- A σ t = refl

p+ : ∀ {Γ} A → Sub (Γ ▶+ A) Γ
p+ {Γ} A = sub ₁ ₁

p+∘ : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → p+ A ∘ (,+ A σ t) ≡ σ
p+∘ = refl

p- : ∀ {Γ} A → Sub (Γ ▶- A) Γ
p- A = sub ₁ ₁

p-∘ : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → p- A ∘ ,- A σ t ≡ σ
p-∘ = refl

op-p+ : ∀ {Γ A} → opS (p+ A) ≡ p- {op Γ} A
op-p+ = refl

q+ : ∀ {Γ} A → Tm (Γ ▶+ A) (A [ p+ A ]T)
q+ {Γ} A = tm ₂ ₂

q+[] : ∀ {Γ Δ A}{σ : Sub Δ Γ}{t} → q+ A [ ,+ A σ t ]t ≡ t
q+[] = refl

-- We have vars pointing to + and =,
-- op-in = is still =
------------------------------------------------------------

_▶=_ : (Γ : Con) → Ty ∙ → Con
Γ ▶= A = con
  (Σ (! Γ) (λ _ → ! A _))
  (λ {(γ₀ , a₀)(γ₁ , a₁) → ΣPP (R Γ γ₀ γ₁) (λ f → R A a₀ a₁ _ ∧ R A a₁ a₀ _)})
  ((rfl Γ) , (rfl A) , (rfl A))
  (λ p q → trs Γ (₁ p) (₁ q) , (trs A (₁ (₂ p)) (₁ (₂ q))) ,
          trs A (q .₂ .₂) (p .₂ .₂))

p= : ∀ {Γ} A → Sub (Γ ▶= A) Γ
p= {Γ} A = sub ₁ ₁

q= : ∀ {Γ} A → Tm (Γ ▶= A) (A [ ε ]T)
q= {Γ} A = tm ₂ λ f → f .₂ .₁

op▶= : ∀ {Γ A} → op (Γ ▶= A) ≡ (op Γ ▶= A)
op▶= {Γ}{A} = con≡
  refl
  (λ x y → propext (λ p → p .₁ , p .₂ .₂ , p .₂ .₁)
                   (λ p → p .₁ , p .₂ .₂ , p .₂ .₁))

op-p= : ∀ {Γ A} → opS (p= {Γ} A) ≃ p= {op Γ} A
op-p= {Γ}{A} = sub≃ (op▶= {Γ}{A}) refl (λ {refl̃ → refl̃})

-- how to do: type which depends on only the ▶= parts in a context
-- ideas: contextual proset? which is always given as an iterated
-- total proset?



-- core : Con → Con
-- core Γ = con
--   (! Γ)
--   (λ x y → R Γ x y ∧ R Γ y x)
--   (rfl Γ , rfl Γ)
--   (λ {(p , q)(p' , q') → (trs Γ p p') , (trs Γ q' q)})

-- coreT+ : ∀ {Γ} → Ty Γ → Ty (core Γ)
-- coreT+ {Γ} A = ty
--   (! A)
--   (λ { {x}{y} xx yy (f , g) → R A xx yy f ∧ R A yy xx g})
--   {!!}
--   {!!}
--   {!!}
--   {!!}
--   {!!}

-- core▶+ : ∀ {Γ A} → core (Γ ▶+ A) ≡ {!core Γ ▶= coreT+ A!}
-- core▶+ = {!!}

-- -- NO GOOD, we don't want to double morphisms in Γ!
-- _▶='_ : (Γ : Con) → Ty (core Γ) → Con
-- Γ ▶=' A =
--   con (Σ (! Γ) (! A))
--       (λ {(x , a)(y , b) → ΣPP (R Γ x y) {!R A a b!}})
--       {!!}
--       {!!}

-- Licata: there is no rule for using contravariant variables!
-- It seems that it can't even be given in the model.

-- It's not an issue because contravariant vars become covariant
-- before we use them.

-- q- : ∀ {Γ A} → Tm (Γ ▶- A) (A [ {!!} ]T)
-- q- {Γ}{A} = {!!}

,+η : ∀ {Γ Δ A}{σ : Sub Γ (Δ ▶+ A)} → σ ≡ ,+ A (p+ A ∘ σ) (q+ A [ σ ]t)
,+η = refl

,+∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ Γ}{t : Tm Δ (A [ σ ]T)}{δ : Sub Σ Δ}
      → ,+ A σ t ∘ δ ≡ ,+ A (σ ∘ δ) (t [ δ ]t)
,+∘ = refl

,-∘ : ∀ {Γ Δ Σ A}{σ : Sub Δ Γ}{t : Tm (op Δ) (A [ opS σ ]T)}{δ : Sub Σ Δ}
      → ,- A σ t ∘ δ ≡ ,- A (σ ∘ δ) (t [ opS δ ]t)
,-∘ = refl


_^+_ : ∀ {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶+ (A [ σ ]T)) (Δ ▶+ A)
_^+_ σ A = sub (λ γ → ! σ (₁ γ) , ₂ γ) (λ p → R σ (₁ p) , ₂ p)
infixl 5 _^+_

_^-_ : ∀ {Γ Δ : Con}(σ : Sub (op Γ) (op Δ))(A : Ty (op Δ)) → Sub (Γ ▶- (A [ σ ]T)) (Δ ▶- A)
_^-_ {Γ} {Δ} σ A = sub (λ {(p , q) → ! σ p , q}) (λ {(p , q) → R σ p , q})
infixl 5 _^-_
