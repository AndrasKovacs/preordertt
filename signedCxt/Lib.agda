{-# OPTIONS --prop --rewriting #-}

module Lib where

open import Agda.Primitive public

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
open Σ public
{-# BUILTIN SIGMA Σ #-}
infixr 4 _,_

record ΣPP (P : Prop) (Q : P → Prop) : Prop where
  constructor _,_
  field
    ₁ : P
    ₂ : Q ₁
open ΣPP public

infixr 4 _∧_
_∧_ : Prop → Prop → Prop
P ∧ Q = ΣPP P (λ _ → Q)

record ΣSP {i j}(A : Set i) (B : A → Prop j) : Set (i ⊔ j) where
  constructor _,_
  field
    ₁ : A
    ₂ : B ₁
open ΣSP public

infix 4 _≡_
data _≡_ {α}{A : Set α}(a : A) : A → Prop where
  refl : a ≡ a
{-# BUILTIN REWRITE _≡_ #-}

postulate
  tr  : ∀ {α β}{A : Set α}(P : A → Set β) {x y : A} → x ≡ y → P x → P y
  trβ : ∀ {α β}{A : Set α}(P : A → Set β) {x : A}{p : x ≡ x}{px : P x}
          → tr P p px ≡ px
{-# REWRITE trβ #-}

trP : ∀ {α β}{A : Set α}(P : A → Prop β) {x y : A} → x ≡ y → P x → P y
trP P refl px = px

infix 3 _∋_
_∋_ : ∀ {α}(A : Set α) → A → A
A ∋ a = a

infix 3 _∋P_
_∋P_ : ∀ {α}(A : Prop α) → A → A
A ∋P a = a

contrSP : ∀ {i}{A : Set i}{x y : A}(p : x ≡ y)
       → (ΣSP A (λ y → x ≡ y) ∋ (x , refl)) ≡ (y , p)
contrSP refl = refl

J : ∀ {i j}{A : Set i}{x : A}(P : ∀ y → x ≡ y → Set j) → P x refl → ∀ {y} p → P y p
J {A = A}{x} P pr {y} p =
  tr {A = ΣSP A (λ y → x ≡ y)} (λ {(y , p) → P y p})
     {x , refl}{y , p} (contrSP p)
     pr

JP : ∀ {i j}{A : Set i}{x : A}(P : ∀ y → x ≡ y → Prop j) → P x refl → ∀ {y} p → P y p
JP {A = A}{x} P pr {y} p =
  trP {A = ΣSP A (λ y → x ≡ y)} (λ {(y , p) → P y p})
     {x , refl}{y , p} (contrSP p)
     pr

postulate
  propext : ∀ {α}{P Q : Prop α} → (P → Q) → (Q → P) → P ≡ Q
  funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → _≡_ f g
  funextP : ∀{i j}{A : Prop i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x ≡ g x) → _≡_ f g
  funexti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ q = q
infixr 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe = tr (λ A → A)

coe-coe : ∀ {i}{A B C : Set i}(p : A ≡ B)(q : B ≡ C)
          → coe (p ◾ q) ≡ (λ x → coe q (coe p x))
coe-coe refl refl = refl

tr-tr : ∀ {i j}{A : Set i}(B : A → Set j){x y z}
         (p : x ≡ y)(q : y ≡ z)
       → tr B (p ◾ q) ≡ (λ x → tr B q (tr B p x))
tr-tr B refl refl = refl

_&_ :
  ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → f a₀ ≡ f a₁
f & refl = refl
infixl 9 _&_

happly : ∀ {i j}{A : Set i}{B : Set j}{f g : A → B} → f ≡ g → ∀ x → f x ≡ g x
happly refl x = refl

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → tr B a₂ (f a₀) ≡ f a₁
apd f refl = refl

record LiftP {i} (P : Prop i) : Set i where
  constructor lift
  field
    lower : P
open LiftP public

data 𝔽 : Prop where

𝔽-elim : ∀ {A : Set} → 𝔽 → A
𝔽-elim ()

record ⊤ : Set where
  constructor tt

record 𝕋 : Prop where
  constructor true
