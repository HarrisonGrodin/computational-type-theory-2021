module Tait where

-- Boilerplate for contexts and substitutions inspired by:
-- https://plfa.github.io/DeBruijn/

-- Proof technique from "How to (Re)Invent Tait's Method":
-- http://www.cs.cmu.edu/~rwh/courses/chtt/pdfs/tait.pdf

open import Data.Sum
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Binary.PropositionalEquality.TrustMe using (trustMe)

infix  4 _⊢_
infix  4 _∋_

infixl 7 _·_
infix  9 `_


data Type : Set where
  unit : Type
  bool : Type
  _∧_  : Type → Type → Type
  _⊃_  : Type → Type → Type

data Ctx : Set where
  ∅   : Ctx
  _#_ : Ctx → Type → Ctx

data All : (p : Type → Set) → Ctx → Set where
  ∅   : ∀ {p} → All p ∅
  _#_ : ∀ {p} → ∀ {Γ A} → All p Γ → p A → All p (Γ # A)

data _∋_ : Ctx → Type → Set where
  Z  : ∀ {Γ A} → (Γ # A) ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A → (Γ # B) ∋ A

ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ # B ∋ A → Δ # B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

data _⊢_ : Ctx → Type → Set where
  `_     : ∀ {Γ A} → Γ ∋ A → Γ ⊢ A
  ⋆      : ∀ {Γ} → Γ ⊢ unit
  yes no : ∀ {Γ} → Γ ⊢ bool
  ⟨_,_⟩  : ∀ {Γ A₁ A₂} → Γ ⊢ A₁ → Γ ⊢ A₂ → Γ ⊢ (A₁ ∧ A₂)
  fst    : ∀ {Γ A₁ A₂} → Γ ⊢ (A₁ ∧ A₂) → Γ ⊢ A₁
  snd    : ∀ {Γ A₁ A₂} → Γ ⊢ (A₁ ∧ A₂) → Γ ⊢ A₂
  ƛ      : ∀ {Γ A₁ A₂} → (Γ # A₁) ⊢ A₂ → Γ ⊢ (A₁ ⊃ A₂)
  _·_    : ∀ {Γ A₁ A₂} → Γ ⊢ (A₁ ⊃ A₂) → Γ ⊢ A₁ → Γ ⊢ A₂

rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)          =  ` (ρ x)
rename ρ ⋆              = ⋆
rename ρ yes            = yes
rename ρ no             = no
rename ρ ⟨ M₁ , M₂ ⟩    = ⟨ rename ρ M₁ , rename ρ M₂ ⟩
rename ρ (fst M)        = fst (rename ρ M)
rename ρ (snd M)        = snd (rename ρ M)
rename ρ (ƛ N)          = ƛ (rename (ext ρ) N)
rename ρ (L · M)        = (rename ρ L) · (rename ρ M)

Subst : (Γ Δ : Ctx) → Set
Subst Γ Δ = ∀ {A} → Γ ∋ A → Δ ⊢ A

exts : ∀ {Γ Δ} → Subst Γ Δ → ∀ {A} → Subst (Γ # A) (Δ # A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

extend : ∀ {Γ Δ A} → Δ ⊢ A → Subst Γ Δ → Subst (Γ # A) Δ
extend M γ Z     = M
extend M γ (S x) = γ x

subst : ∀ {Γ Δ} → Subst Γ Δ → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)       = σ x
subst σ ⋆           = ⋆
subst σ yes         = yes
subst σ no          = no
subst σ ⟨ M₁ , M₂ ⟩ = ⟨ subst σ M₁ , subst σ M₂ ⟩
subst σ (fst M)     = fst (subst σ M)
subst σ (snd M)     = snd (subst σ M)
subst σ (ƛ M)       = ƛ (subst (exts σ) M)
subst σ (M₁ · M₂)   = subst σ M₁ · subst σ M₂

_[_] : ∀ {Γ A B}
  → Γ # B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ # B} {Γ} (extend M `_) {A} N

data _final : ∀ {A} → ∅ ⊢ A → Set where
  yes  : yes final
  no   : no final
  ⋆    : ⋆ final
  pair : ∀ {A₁ A₂} → (M₁ : ∅ ⊢ A₁) → (M₂ : ∅ ⊢ A₂) → ⟨ M₁ , M₂ ⟩ final
  ƛ    : ∀ {A₁ A₂} → (M : (∅ # A₁) ⊢ A₂) → (ƛ M) final

data _↦_ : {A : Type} → ∅ ⊢ A → ∅ ⊢ A → Set where
  fst-step : ∀ {A₁ A₂} → {M M' : ∅ ⊢ A₁ ∧ A₂} → (M ↦ M') → (fst M ↦ fst M')
  snd-step : ∀ {A₁ A₂} → {M M' : ∅ ⊢ A₁ ∧ A₂} → (M ↦ M') → (snd M ↦ snd M')
  fst      : ∀ {A₁ A₂} → {M₁ : ∅ ⊢ A₁} → {M₂ : ∅ ⊢ A₂} → (fst ⟨ M₁ , M₂ ⟩ ↦ M₁)
  snd      : ∀ {A₁ A₂} → {M₁ : ∅ ⊢ A₁} → {M₂ : ∅ ⊢ A₂} → (snd ⟨ M₁ , M₂ ⟩ ↦ M₂)
  app-step : ∀ {A₁ A₂} → {M₁ M₁' : ∅ ⊢ A₁ ⊃ A₂} → {M₂ : ∅ ⊢ A₁} → (M₁ ↦ M₁') → (M₁ · M₂) ↦ (M₁' · M₂)
  app      : ∀ {A₁ A₂} → {M : ∅ # A₁ ⊢ A₂} → {M₂ : ∅ ⊢ A₁} → (ƛ M · M₂) ↦ (M [ M₂ ])

data _↦*_ : {A : Type} → ∅ ⊢ A → ∅ ⊢ A → Set where
  refl : ∀ {A} → {M : ∅ ⊢ A} → M ↦* M
  step : ∀ {A} → {M M' M'' : ∅ ⊢ A} → M ↦ M' → M' ↦* M'' → M ↦* M''

step-trans : ∀ {A} → {M M' M'' : ∅ ⊢ A} → M ↦* M' → M' ↦* M'' → M ↦* M''
step-trans refl        s₂ = s₂
step-trans (step x s₁) s₂ = step x (step-trans s₁ s₂)

compatible : ∀ {A B} → ∀ {M M' : ∅ ⊢ A} → {p : ∅ ⊢ A → ∅ ⊢ B} → (∀ {N N'} → N ↦ N' → p N ↦ p N') → M ↦* M' → p M ↦* p M'
compatible lift refl       = refl
compatible lift (step x s) = step (lift x) (compatible lift s)

ht : (A : Type) → ∅ ⊢ A → Set
ht unit      M = M ↦* ⋆
ht bool      M = (M ↦* yes) ⊎ (M ↦* no)
ht (A₁ ∧ A₂) M = ∃ λ N₁ → ∃ λ N₂ → (M ↦* ⟨ N₁ , N₂ ⟩) × (ht A₁ N₁ × ht A₂ N₂)
ht (A₂ ⊃ A)  M = ∃ λ N → (M ↦* ƛ N) × (∀ N₂ → ht A₂ N₂ → ht A (N [ N₂ ]))

HT : ∀ {Γ} → Subst Γ ∅ → Set
HT {Γ} γ = ∀ {A} → (x : Γ ∋ A) → ht A (γ x)

ht-reverse-step : ∀ {A M M'} → M ↦ M' → ht A M' → ht A M
ht-reverse-step {unit}   = step
ht-reverse-step {bool}   s = [ (inj₁ ∘ step s) , (inj₂ ∘ step s) ]
ht-reverse-step {A ∧ A₁} s (N₁ , N₂ , term , ht₁ , ht₂) = N₁ , N₂ , step s term , ht₁ , ht₂
ht-reverse-step {A ⊃ A₁} s (N , term , ht') = N , step s term , ht'

ht-reverse-steps : ∀ {A M M'} → M ↦* M' → ht A M' → ht A M
ht-reverse-steps refl       h = h
ht-reverse-steps (step x s) h = ht-reverse-step x (ht-reverse-steps s h)

_>>_∋_ : (Γ : Ctx) → (A : Type) → Γ ⊢ A → Set
Γ >> A ∋ M = (γ : Subst Γ ∅) → (h : HT γ) → ht A (subst γ M)

tait : ∀ {Γ A} → (M : Γ ⊢ A) → Γ >> A ∋ M
tait (` x)       γ h = h x
tait ⋆           γ h = refl
tait yes         γ h = inj₁ refl
tait no          γ h = inj₂ refl
tait ⟨ M₁ , M₂ ⟩ γ h = subst γ M₁ , subst γ M₂ , refl , tait M₁ γ h , tait M₂ γ h
tait (fst M)     γ h = let _ , _ , step-to-pair , ht-M₁ , _ = tait M γ h in
                       ht-reverse-steps (step-trans (compatible fst-step step-to-pair) (step fst refl)) ht-M₁
tait (snd M)     γ h = let _ , _ , step-to-pair , _ , ht-M₂ = tait M γ h in
                       ht-reverse-steps (step-trans (compatible snd-step step-to-pair) (step snd refl)) ht-M₂
tait (ƛ M₂)      γ h = subst (exts γ) M₂ , refl , λ M₁ ht₁ →
                         let ht₂ = tait M₂ (extend M₁ γ) λ { Z → ht₁ ; (S x) → h x } in
                         Eq.subst (ht _) trustMe ht₂  -- FIXME
tait (M₁ · M₂)   γ h = let _ , step-to-lam , ht₁ = tait M₁ γ h in
                       let ht₂ = tait M₂ γ h in
                       ht-reverse-steps (step-trans (compatible app-step step-to-lam) (step app refl)) (ht₁ (subst γ M₂) ht₂ )

subst-lemma : ∀ {Γ A} → (M : Γ ⊢ A) → subst `_ M ≡ M
subst-lemma (` x)       = Eq.refl
subst-lemma ⋆           = Eq.refl
subst-lemma yes         = Eq.refl
subst-lemma no          = Eq.refl
subst-lemma ⟨ M₁ , M₂ ⟩ = Eq.cong₂ ⟨_,_⟩ (subst-lemma M₁) (subst-lemma M₂)
subst-lemma (fst M)     = Eq.cong fst (subst-lemma M)
subst-lemma (snd M)     = Eq.cong snd (subst-lemma M)
subst-lemma {Γ} (ƛ M)   = trustMe  -- FIXME
subst-lemma (M₁ · M₂)   = Eq.cong₂ _·_ (subst-lemma M₁) (subst-lemma M₂)

bools-terminate : (M : ∅ ⊢ bool) → M ↦* yes ⊎ M ↦* no
bools-terminate M = Eq.subst (λ M → M ↦* yes ⊎ M ↦* no) (subst-lemma M) (tait M `_ (λ {_} ()))
