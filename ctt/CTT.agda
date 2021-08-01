-- Formalization of OPLSS: Computational Type Theory (Robert Harper), 2018.

module CTT where

open import Level
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Data.Product renaming (_×_ to _∧_)

private
  variable
    ℓ : Level

Deterministic : {A B : Set} (_⇒_ : REL A B ℓ) → Set ℓ
Deterministic {A = A} {B = B} _⇒_ = {M : A} {M'₁ M'₂ : B} → M ⇒ M'₁ → M ⇒ M'₂ → M'₁ ≡ M'₂

record Language : Set₁ where
  field
    exp : Set
    _val : exp → Set
    _↦_ : exp → exp → Set

    val-↦-exclusive : {M : exp} → ¬ (M val ∧ ∃ λ M' → M ↦ M')
    ↦-deterministic : Deterministic _↦_

per-refl : {A : Set} {_≈_ : Rel A ℓ} {M M' : A} → IsPartialEquivalence _≈_ → M ≈ M' → M ≈ M
per-refl record { sym = sym ; trans = trans } h = trans h (sym h)

module MultiStep (L : Language) where
  open Language L

  data _↦*_ : exp → exp → Set where
    here : {M : exp} → M ↦* M
    step : {M M' M'' : exp} → M ↦ M' → M' ↦* M'' → M ↦* M''

  ↦*-append : {M M' M'' : exp} → M ↦* M' → M' ↦* M'' → M ↦* M''
  ↦*-append here M↦*M'' = M↦*M''
  ↦*-append (step M↦M''' M'''↦*M') M'↦*M'' = step M↦M''' (↦*-append M'''↦*M' M'↦*M'')

  stepʳ : {M M' M'' : exp} → M ↦* M' → M' ↦ M'' → M ↦* M''
  stepʳ M↦*M' M'↦M'' = ↦*-append M↦*M' (step M'↦M'' here)

  -- ↦*-deterministic : Deterministic _↦*_
  -- ↦*-deterministic here here = refl
  -- ↦*-deterministic (here {h}) (step x h') = {!   !}
  -- ↦*-deterministic (step x h) (here {h'}) = {!   !}
  -- ↦*-deterministic (step M↦M'₁ M'₁↦*M''₁) (step M↦M'₂ M'₂↦*M''₂) with ↦-deterministic M↦M'₁ M↦M'₂
  -- ... | refl = ↦*-deterministic M'₁↦*M''₁ M'₂↦*M''₂

  record _⇓_ (M M' : exp) : Set where
    constructor _and_
    field
      M↦*M' : M ↦* M'
      M'val : M' val

  step⇓ : {M M' M'' : exp} → M ↦ M' → M' ⇓ M'' → M ⇓ M''
  step⇓ h (M↦*M' and M'val) = step h M↦*M' and M'val

  ⇓-deterministic : Deterministic _⇓_
  ⇓-deterministic (M↦*M'₁ and M'₁val) (M↦*M'₂ and M'val₂) = aux M↦*M'₁ M↦*M'₂ M'₁val M'val₂
    where
      aux : {M : exp} {M'₁ M'₂ : exp} → M ↦* M'₁ → M ↦* M'₂ → M'₁ val → M'₂ val → M'₁ ≡ M'₂
      aux here here _ _ = refl
      aux here (step M↦M' _) Mval _ = contradiction (Mval , _ , M↦M') val-↦-exclusive
      aux (step M↦M' _) here _ Mval = contradiction (Mval , _ , M↦M') val-↦-exclusive
      aux (step M↦M'₁ M'₁↦*M''₁) (step M↦M'₂ M'₂↦*M'') M''₁val M''₂val with ↦-deterministic M↦M'₁ M↦M'₂
      ... | refl = aux M'₁↦*M''₁ M'₂↦*M'' M''₁val M''₂val

module Example1 where
  -- Language

  data exp : Set where
    Bool : exp
    tt ff : exp
    if : exp → exp → exp → exp
    _×_ : exp → exp → exp
    ⟨_,_⟩ : exp → exp → exp
    _·1 : exp → exp
    _·2 : exp → exp


  data _val : exp → Set where
    Bool : Bool val
    tt : tt val
    ff : ff val
    _×_ : {A₁ A₂ : exp} → (A₁ × A₂) val
    ⟨_,_⟩ : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ val

  infix 3 _↦_
  data _↦_ : exp → exp → Set where
    if/principal : {M M' M₁ M₀ : exp} → M ↦ M' → if M M₁ M₀ ↦ if M' M₁ M₀
    if/tt : (M₁ M₀ : exp) → if tt M₁ M₀ ↦ M₁
    if/ff : (M₁ M₀ : exp) → if ff M₁ M₀ ↦ M₀
    _·1/principal : {M M' : exp} → M ↦ M' → M ·1 ↦ M' ·1
    _·1 : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ ·1 ↦ M₁
    _·2/principal : {M M' : exp} → M ↦ M' → M ·2 ↦ M' ·2
    _·2 : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ ·2 ↦ M₂

  ↦-deterministic : Deterministic _↦_
  ↦-deterministic (if/principal h) (if/principal h') with ↦-deterministic h h'
  ... | refl = refl
  ↦-deterministic (if/tt _ M₀) (if/tt _ .M₀) = refl
  ↦-deterministic (if/ff M₁ _) (if/ff .M₁ _) = refl
  ↦-deterministic (h ·1/principal) (h' ·1/principal) with ↦-deterministic h h'
  ... | refl = refl
  ↦-deterministic _·1 _·1 = refl
  ↦-deterministic (h ·2/principal) (h' ·2/principal) with ↦-deterministic h h'
  ... | refl = refl
  ↦-deterministic _·2 _·2 = refl

  val-↦-exclusive : {M : exp} → ¬ ((M val) ∧ ∃ (_↦_ M))
  val-↦-exclusive (Bool , _ , ())
  val-↦-exclusive (tt , _ , ())
  val-↦-exclusive (ff , _ , ())
  val-↦-exclusive (_×_ , _ , ())
  val-↦-exclusive (⟨_,_⟩ , _ , ())

  open MultiStep
    record
      { exp = exp
      ; _val = _val
      ; _↦_ = _↦_
      ; val-↦-exclusive = val-↦-exclusive
      ; ↦-deterministic = ↦-deterministic
      }


  module Type where
    data _≐_typeᵒ : exp → exp → Set where
      Bool : Bool ≐ Bool typeᵒ
      _×_ : {A₁ A₁' A₂ A₂' : exp} →
        A₁ ≐ A₁' typeᵒ →
        A₂ ≐ A₂' typeᵒ →
        (A₁ × A₂) ≐ (A₁' × A₂') typeᵒ

    _typeᵒ : exp → Set
    A typeᵒ = A ≐ A typeᵒ

    record _≐_type (A A' : exp) : Set where
      constructor ⇓_,⇓_,_
      field
        {Aᵒ} : exp
        A⇓Aᵒ : A ⇓ Aᵒ
        {A'ᵒ} : exp
        A'⇓A'ᵒ : A' ⇓ A'ᵒ
        Aᵒ≐A'ᵒtypeᵒ : Aᵒ ≐ A'ᵒ typeᵒ

    _type : exp → Set
    A type = A ≐ A type

    ≐typeᵒ-isPartialEquivalence : IsPartialEquivalence (_≐_typeᵒ)
    ≐typeᵒ-isPartialEquivalence = record { sym = sym ; trans = trans }
      where
        sym : Symmetric _≐_typeᵒ
        sym Bool = Bool
        sym (h₁ × h₂) = sym h₁ × sym h₂

        trans : Transitive _≐_typeᵒ
        trans Bool Bool = Bool
        trans (h₁ × h₂) (h₁' × h₂') = trans h₁ h₁' × trans h₂ h₂'

  module Membership where
    data R/Bool : exp → exp → Set where
      tt : R/Bool tt tt
      ff : R/Bool ff ff

    data _∋ᵒ_≐_ : (A : exp) → exp → exp → Set
    record _∋_≐_ (A : exp) (M M' : exp) : Set

    A∋ᵒ≐-isPartialEquivalence : (A : exp) → IsPartialEquivalence (A ∋ᵒ_≐_)
    A∋≐-isPartialEquivalence : (A : exp) → IsPartialEquivalence (A ∋_≐_)

    data _∋ᵒ_≐_ where
      Bool : {M M' : exp} → R/Bool M M' → Bool ∋ᵒ M ≐ M'
      _×_ : {A₁ A₂ M₁ M₂ M₁' M₂' : exp} →
        A₁ ∋ M₁ ≐ M₁' →
        A₂ ∋ M₂ ≐ M₂' →
        (A₁ × A₂) ∋ᵒ ⟨ M₁ , M₂ ⟩ ≐ ⟨ M₁' , M₂' ⟩

    _∋ᵒ_ : (A : exp) → exp → Set
    A ∋ᵒ M = A ∋ᵒ M ≐ M

    A∋ᵒ≐-isPartialEquivalence A = record { sym = sym ; trans = trans }
      where
        sym : {A : exp} → Symmetric (A ∋ᵒ_≐_)
        sym (Bool tt) = Bool tt
        sym (Bool ff) = Bool ff
        sym {A₁ × A₂} (h₁ × h₂) = IsPartialEquivalence.sym (A∋≐-isPartialEquivalence A₁) h₁ × IsPartialEquivalence.sym (A∋≐-isPartialEquivalence A₂) h₂

        trans : {A : exp} → Transitive (A ∋ᵒ_≐_)
        trans (Bool tt) (Bool tt) = Bool tt
        trans (Bool ff) (Bool ff) = Bool ff
        trans {A₁ × A₂} (h₁ × h₂) (h₁' × h₂') = IsPartialEquivalence.trans (A∋≐-isPartialEquivalence A₁) h₁ h₁' × IsPartialEquivalence.trans (A∋≐-isPartialEquivalence A₂) h₂ h₂'

    record _∋_≐_ A M M' where
      constructor ⇓_,⇓_,_
      pattern
      inductive
      field
        {Mᵒ} : exp
        M⇓Mᵒ : M ⇓ Mᵒ
        {M'ᵒ} : exp
        M'⇓M'ᵒ : M' ⇓ M'ᵒ
        A∋ᵒMᵒ≐M'ᵒ : A ∋ᵒ Mᵒ ≐ M'ᵒ

    _∋_ : (A : exp) → exp → Set
    A ∋ M = A ∋ M ≐ M

    A∋≐-isPartialEquivalence A = record { sym = sym A ; trans = trans A }
      where
        sym : (A : exp) → Symmetric (A ∋_≐_)
        sym A (⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ) = ⇓ M'⇓M'ᵒ ,⇓ M⇓Mᵒ , IsPartialEquivalence.sym (A∋ᵒ≐-isPartialEquivalence A) A∋ᵒMᵒ≐M'ᵒ

        trans : (A : exp) → Transitive (A ∋_≐_)
        trans A {M₀} {M₁} {M₂} (⇓ M₀⇓ ,⇓ M₁⇓ , A∋ᵒMᵒ≐M'ᵒ₁) (⇓ M₁⇓' ,⇓ M₂⇓ , A∋ᵒM'ᵒ₁≐M'ᵒ) with ⇓-deterministic M₁⇓ M₁⇓'
        ... | refl = ⇓ M₀⇓ ,⇓ M₂⇓ , (IsPartialEquivalence.trans (A∋ᵒ≐-isPartialEquivalence A) A∋ᵒMᵒ≐M'ᵒ₁ A∋ᵒM'ᵒ₁≐M'ᵒ)

    -- Lemmas

    rev-closure : {A M M' : exp} → M ↦ M' → A ∋ M' → A ∋ M
    rev-closure M↦M' (⇓ if⇓Mᵒ ,⇓ if⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ) = ⇓ step⇓ M↦M' if⇓Mᵒ ,⇓ step⇓ M↦M' if⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ

    rev-closure* : {A M M' : exp} → M ↦* M' → A ∋ M' → A ∋ M
    rev-closure* here A∋M' = A∋M'
    rev-closure* (step M↦M'' M''↦*M') A∋M' = rev-closure M↦M'' (rev-closure* M''↦*M' A∋M')

    lift-principal : (f : exp → exp) → ({M M' : exp} → M ↦ M' → f M ↦ f M') → {M M' : exp} → M ↦* M' → f M ↦* f M'
    lift-principal f h here = here
    lift-principal f h (step M↦M'' M''↦*M') = step (h M↦M'') (lift-principal f h M''↦*M')


  open Type
  open Membership

  -- Facts

  fact/if : {A M M₁ M₀ M₁' M₀' : exp} → Bool ∋ M → A ∋ M₁ → A ∋ M₀ → A ∋ if M M₁ M₀
  fact/if {M₁ = M₁} {M₀ = M₀} (⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool tt) h₁ h₀ = rev-closure* (stepʳ (lift-principal (λ M → if M M₁ M₀) if/principal (_⇓_.M↦*M' M'⇓M'ᵒ)) (if/tt M₁ M₀)) h₁
  fact/if {M₁ = M₁} {M₀ = M₀} (⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool ff) h₁ h₀ = rev-closure* (stepʳ (lift-principal (λ M → if M M₁ M₀) if/principal (_⇓_.M↦*M' M'⇓M'ᵒ)) (if/ff M₁ M₀)) h₀

  fact/·1 : {A₁ A₂ M : exp} → (A₁ × A₂) ∋ M → A₁ ∋ (M ·1)
  fact/·1 {A₁ = A₁} (⇓ M⇓⟨M₁,M₂⟩ ,⇓ M⇓⟨M₁',M₂'⟩ , (A₁∋M₁≐M₁' × A₂∋M₂≐M₂')) =
    rev-closure* (stepʳ (lift-principal _·1 _·1/principal (_⇓_.M↦*M' M⇓⟨M₁,M₂⟩)) _·1) (per-refl (A∋≐-isPartialEquivalence A₁) A₁∋M₁≐M₁')

  fact/⟨,⟩·1 : {A₁ M₁ M₂ : exp} → A₁ ∋ M₁ → A₁ ∋ ⟨ M₁ , M₂ ⟩ ·1 ≐ M₁
  fact/⟨,⟩·1 (⇓ M₁⇓Mᵒ ,⇓ M₁⇓M'ᵒ , A₁∋ᵒMᵒ≐M'ᵒ) = ⇓ step⇓ _·1 M₁⇓Mᵒ ,⇓ M₁⇓M'ᵒ , A₁∋ᵒMᵒ≐M'ᵒ
