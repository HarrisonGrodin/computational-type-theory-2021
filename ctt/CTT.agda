{-# OPTIONS --no-positivity-check #-}

-- Formalization of OPLSS: Computational Type Theory (Robert Harper), 2018.

module CTT where

open import Function using (_$_)
open import Level using (Level)
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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

  lift-principal : (f : exp → exp) → ({M M' : exp} → M ↦ M' → f M ↦ f M') → {M M' : exp} → M ↦* M' → f M ↦* f M'
  lift-principal f h here = here
  lift-principal f h (step M↦M'' M''↦*M') = step (h M↦M'') (lift-principal f h M''↦*M')

  record _⇓_ (M M' : exp) : Set where
    constructor _and_
    field
      M↦*M' : M ↦* M'
      M'val : M' val

  step⇓ : {M M' M'' : exp} → M ↦ M' → M' ⇓ M'' → M ⇓ M''
  step⇓ M↦*M' (M'↦*M'' and M''val) = step M↦*M' M'↦*M'' and M''val

  step*⇓ : {M M' M'' : exp} → M ↦* M' → M' ⇓ M'' → M ⇓ M''
  step*⇓ M↦*M' (M'↦*M'' and M''val) = ↦*-append M↦*M' M'↦*M'' and M''val

  val⇓ : {M : exp} → M val → M ⇓ M
  val⇓ Mval = here and Mval

  ⇓-deterministic : Deterministic _⇓_
  ⇓-deterministic (M↦*M'₁ and M'₁val) (M↦*M'₂ and M'val₂) = aux M↦*M'₁ M↦*M'₂ M'₁val M'val₂
    where
      aux : {M : exp} {M'₁ M'₂ : exp} → M ↦* M'₁ → M ↦* M'₂ → M'₁ val → M'₂ val → M'₁ ≡ M'₂
      aux here here _ _ = refl
      aux here (step M↦M' _) Mval _ = contradiction (Mval , -, M↦M') val-↦-exclusive
      aux (step M↦M' _) here _ Mval = contradiction (Mval , -, M↦M') val-↦-exclusive
      aux (step M↦M'₁ M'₁↦*M''₁) (step M↦M'₂ M'₂↦*M'') M''₁val M''₂val with ↦-deterministic M↦M'₁ M↦M'₂
      ... | refl = aux M'₁↦*M''₁ M'₂↦*M'' M''₁val M''₂val

  val⇓val : {M M' : exp} → M val → M ⇓ M' → M' ≡ M
  val⇓val Mval M⇓M' with ⇓-deterministic (val⇓ Mval) M⇓M'
  ... | refl = refl

module Example1 where
  -- Language

  data exp : Set where
    Bool : exp
    tt ff : exp
    if : exp → exp → exp → exp
    Nat : exp
    zero : exp
    succ : exp → exp
    rec : exp → (exp → exp → exp) → exp → exp
    _×_ : exp → exp → exp
    ⟨_,_⟩ : exp → exp → exp
    _·1 : exp → exp
    _·2 : exp → exp
    Eq : exp → exp → exp → exp
    refl : exp


  data _val : exp → Set where
    Bool : Bool val
    tt : tt val
    ff : ff val
    Nat : Nat val
    zero : zero val
    succ : {M : exp} → succ M val
    _×_ : {A₁ A₂ : exp} → A₁ val → A₂ val → (A₁ × A₂) val
    ⟨_,_⟩ : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ val
    Eq : {A M₁ M₂ : exp} → Eq A M₁ M₂ val
    refl : refl val

  infix 3 _↦_
  data _↦_ : exp → exp → Set where
    if/principal : {M M' M₁ M₀ : exp} → M ↦ M' → if M M₁ M₀ ↦ if M' M₁ M₀
    if/tt : {M₁ M₀ : exp} → if tt M₁ M₀ ↦ M₁
    if/ff : {M₁ M₀ : exp} → if ff M₁ M₀ ↦ M₀
    rec/principal : ∀ {M M' M₀ M₁} → M ↦ M' → rec M₀ M₁ M ↦ rec M₀ M₁ M'
    rec/zero : ∀ {M₀ M₁} → rec M₀ M₁ zero ↦ M₀
    rec/succ : ∀ {M M₀ M₁} → rec M₀ M₁ (succ M) ↦ M₁ M (rec M₀ M₁ M)
    _·1/principal : {M M' : exp} → M ↦ M' → M ·1 ↦ M' ·1
    _·1 : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ ·1 ↦ M₁
    _·2/principal : {M M' : exp} → M ↦ M' → M ·2 ↦ M' ·2
    _·2 : {M₁ M₂ : exp} → ⟨ M₁ , M₂ ⟩ ·2 ↦ M₂

  ↦-deterministic : Deterministic _↦_
  ↦-deterministic (if/principal h) (if/principal h') with ↦-deterministic h h'
  ... | refl = refl
  ↦-deterministic if/tt if/tt = refl
  ↦-deterministic if/ff if/ff = refl
  ↦-deterministic (rec/principal h) (rec/principal h') with ↦-deterministic h h'
  ... | refl = refl
  ↦-deterministic rec/zero rec/zero = refl
  ↦-deterministic rec/succ rec/succ = refl
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
  val-↦-exclusive (_ × _ , _ , ())
  val-↦-exclusive (⟨_,_⟩ , _ , ())

  open MultiStep
    record
      { exp = exp
      ; _val = _val
      ; _↦_ = _↦_
      ; val-↦-exclusive = val-↦-exclusive
      ; ↦-deterministic = ↦-deterministic
      }

  -- Type Signatures

  data _≐_typeᵒ : exp → exp → Set
  record _≐_type (A A' : exp) : Set

  ≐typeᵒ-sym : Symmetric _≐_typeᵒ
  ≐typeᵒ-trans : Transitive _≐_typeᵒ
  ≐typeᵒ-isPartialEquivalence : IsPartialEquivalence (_≐_typeᵒ)

  ≐type-sym : Symmetric _≐_type
  ≐type-trans : Transitive _≐_type
  ≐type-isPartialEquivalence : IsPartialEquivalence (_≐_type)

  data _∋ᵒ_≐_ : (A : exp) → exp → exp → Set
  record _∋_≐_ (A : exp) (M M' : exp) : Set

  A∋ᵒ≐-sym : {A : exp} → Symmetric (A ∋ᵒ_≐_)
  A∋ᵒ≐-trans : {A : exp} → Transitive (A ∋ᵒ_≐_)
  A∋ᵒ≐-isPartialEquivalence : (A : exp) → IsPartialEquivalence (A ∋ᵒ_≐_)

  A∋≐-sym : {A : exp} → Symmetric (A ∋_≐_)
  A∋≐-trans : {A : exp} → Transitive (A ∋_≐_)
  A∋≐-isPartialEquivalence : (A : exp) → IsPartialEquivalence (A ∋_≐_)

  lemma/moveᵒ : {A A' M₁ M₂ : exp} → A ≐ A' typeᵒ → A' ∋ᵒ M₁ ≐ M₂ → A ∋ᵒ M₁ ≐ M₂
  lemma/move : {A A' M₁ M₂ : exp} → A ≐ A' type → A' ∋ M₁ ≐ M₂ → A ∋ M₁ ≐ M₂

  -- Implementations

  data _≐_typeᵒ where
    Bool : Bool ≐ Bool typeᵒ
    Nat : Nat ≐ Nat typeᵒ
    _×_ : {A₁ A₁' A₂ A₂' : exp} →
      A₁ ≐ A₁' typeᵒ →
      A₂ ≐ A₂' typeᵒ →
      (A₁ × A₂) ≐ (A₁' × A₂') typeᵒ
    Eq : {A A' M₁ M₁' M₂ M₂' : exp} →
      A ≐ A' type →
      A ∋ M₁ ≐ M₁' →
      A ∋ M₂ ≐ M₂' →
      Eq A M₁ M₂ ≐ Eq A' M₁' M₂' typeᵒ

  _typeᵒ : exp → Set
  A typeᵒ = A ≐ A typeᵒ

  record _≐_type A A' where
    constructor ⇓_,⇓_,_
    pattern
    inductive
    field
      {Aᵒ} : exp
      A⇓Aᵒ : A ⇓ Aᵒ
      {A'ᵒ} : exp
      A'⇓A'ᵒ : A' ⇓ A'ᵒ
      Aᵒ≐A'ᵒtypeᵒ : Aᵒ ≐ A'ᵒ typeᵒ

  _type : exp → Set
  A type = A ≐ A type

  ⇓_,⇓-,_ : {A Aᵒ : exp} (A⇓Aᵒ : A ⇓ Aᵒ) (Aᵒtypeᵒ : Aᵒ typeᵒ) → A type
  ⇓ A⇓Aᵒ ,⇓-, Aᵒtypeᵒ = ⇓ A⇓Aᵒ ,⇓ A⇓Aᵒ , Aᵒtypeᵒ

  ≐typeᵒ-sym Bool = Bool
  ≐typeᵒ-sym Nat = Nat
  ≐typeᵒ-sym (h₁ × h₂) = ≐typeᵒ-sym h₁ × ≐typeᵒ-sym h₂
  ≐typeᵒ-sym (Eq h h₁ h₂) = Eq (≐type-sym h) (A∋≐-sym (lemma/move (≐type-sym h) h₁)) (A∋≐-sym (lemma/move (≐type-sym h) h₂))

  ≐typeᵒ-trans Bool Bool = Bool
  ≐typeᵒ-trans Nat Nat = Nat
  ≐typeᵒ-trans (h₁ × h₂) (h₁' × h₂') = ≐typeᵒ-trans h₁ h₁' × ≐typeᵒ-trans h₂ h₂'
  ≐typeᵒ-trans (Eq h h₁ h₂) (Eq h' h₁' h₂') = Eq (≐type-trans h h') (A∋≐-trans h₁ (lemma/move h h₁')) (A∋≐-trans h₂ (lemma/move h h₂'))

  ≐typeᵒ-isPartialEquivalence = record { sym = ≐typeᵒ-sym ; trans = ≐typeᵒ-trans }

  ≐type-sym (⇓ A⇓Aᵒ ,⇓ A'⇓A'ᵒ , Aᵒ≐A'ᵒtypeᵒ) = ⇓ A'⇓A'ᵒ ,⇓ A⇓Aᵒ , (≐typeᵒ-sym Aᵒ≐A'ᵒtypeᵒ)

  ≐type-trans {A₀} {A₁} {A₂} (⇓ A₀⇓ ,⇓ A₁⇓ , Aᵒ≐A'ᵒtypeᵒ) (⇓ A₁⇓' ,⇓ A₂⇓ , Aᵒ₁≐A'ᵒ₁typeᵒ) with ⇓-deterministic A₁⇓ A₁⇓'
  ... | refl = ⇓ A₀⇓ ,⇓ A₂⇓ , ≐typeᵒ-trans Aᵒ≐A'ᵒtypeᵒ Aᵒ₁≐A'ᵒ₁typeᵒ

  ≐type-isPartialEquivalence = record { sym = ≐type-sym ; trans = ≐type-trans }

  typeᵒ-val : {A A' : exp} → A ≐ A' typeᵒ → A val
  typeᵒ-val Bool = Bool
  typeᵒ-val Nat = Nat
  typeᵒ-val (h₁ × h₂) = typeᵒ-val h₁ × typeᵒ-val h₂
  typeᵒ-val (Eq h h₁ h₂) = Eq

  typeᵒ-val' : {A A' : exp} → A ≐ A' typeᵒ → A' val
  typeᵒ-val' Bool = Bool
  typeᵒ-val' Nat = Nat
  typeᵒ-val' (h₁ × h₂) = typeᵒ-val' h₁ × typeᵒ-val' h₂
  typeᵒ-val' (Eq h h₁ h₂) = Eq

  typeᵒ-type : {A A' : exp} → A ≐ A' typeᵒ → A ≐ A' type
  typeᵒ-type A≐A'typeᵒ = ⇓ (val⇓ (typeᵒ-val A≐A'typeᵒ)) ,⇓ (val⇓ (typeᵒ-val' A≐A'typeᵒ)) , A≐A'typeᵒ

  data R/Bool : exp → exp → Set where
    tt : {M M' : exp} → M ⇓ tt → M' ⇓ tt → R/Bool M M'
    ff : {M M' : exp} → M ⇓ ff → M' ⇓ ff → R/Bool M M'

  R/Bool-sym : Symmetric R/Bool
  R/Bool-sym (tt h h') = tt h' h
  R/Bool-sym (ff h h') = ff h' h

  R/Bool-trans : Transitive R/Bool
  R/Bool-trans (tt h _) (tt _ h') = tt h h'
  R/Bool-trans (tt _ h) (ff h' _) with ⇓-deterministic h h'
  ... | ()
  R/Bool-trans (ff _ h) (tt h' _) with ⇓-deterministic h h'
  ... | ()
  R/Bool-trans (ff h _) (ff _ h') = ff h h'

  R/Bool-isPartialEquivalence : IsPartialEquivalence R/Bool
  R/Bool-isPartialEquivalence = record { sym = R/Bool-sym ; trans = R/Bool-trans }

  data R/Nat : exp → exp → Set where
    zero : {M M' : exp} → M ⇓ zero → M' ⇓ zero → R/Nat M M'
    succ : {M M' N N' : exp} → M ⇓ succ N → M' ⇓ succ N' → R/Nat N N' → R/Nat M M'

  R/Nat-sym : Symmetric R/Nat
  R/Nat-sym (zero h h') = zero h' h
  R/Nat-sym (succ h h' r) = succ h' h (R/Nat-sym r)

  R/Nat-trans : Transitive R/Nat
  R/Nat-trans (zero h _) (zero _ h') = zero h h'
  R/Nat-trans (zero _ h₁) (succ h₁' _ _) with ⇓-deterministic h₁ h₁'
  ... | ()
  R/Nat-trans (succ _ h₁ _) (zero h₁' _)  with ⇓-deterministic h₁ h₁'
  ... | ()
  R/Nat-trans (succ h h₁ r) (succ h₁' h' r') with ⇓-deterministic h₁ h₁'
  ... | refl = succ h h' (R/Nat-trans r r')

  R/Nat-isPartialEquivalence : IsPartialEquivalence R/Nat
  R/Nat-isPartialEquivalence = record { sym = R/Nat-sym ; trans = R/Nat-trans }

  data R/Eq : exp → exp → Set where
    refl : {M M' : exp} → M ⇓ refl → M' ⇓ refl → R/Eq M M'

  R/Eq-sym : Symmetric R/Eq
  R/Eq-sym (refl h h') = refl h' h

  R/Eq-trans : Transitive R/Eq
  R/Eq-trans (refl h₁ h₁') (refl h₂ h₂') = refl h₁ h₂'

  R/Eq-isPartialEquivalence : IsPartialEquivalence R/Eq
  R/Eq-isPartialEquivalence = record { sym = R/Eq-sym ; trans = R/Eq-trans }

  data _∋ᵒ_≐_ where
    Bool : {M M' : exp} → R/Bool M M' → Bool ∋ᵒ M ≐ M'
    Nat : {M M' : exp} → R/Nat M M' → Nat ∋ᵒ M ≐ M'
    _×_ : {A₁ A₂ M₁ M₂ M₁' M₂' : exp} →
      A₁ ∋ M₁ ≐ M₁' →
      A₂ ∋ M₂ ≐ M₂' →
      (A₁ × A₂) ∋ᵒ ⟨ M₁ , M₂ ⟩ ≐ ⟨ M₁' , M₂' ⟩
    Eq : {A M₁ M₂ M M' : exp} →
      R/Eq M M' →
      A ∋ M₁ ≐ M₂ →
      Eq A M₁ M₂ ∋ᵒ M ≐ M'

  _∋ᵒ_ : (A : exp) → exp → Set
  A ∋ᵒ M = A ∋ᵒ M ≐ M

  A∋ᵒ≐-sym (Bool h) = Bool (R/Bool-sym h)
  A∋ᵒ≐-sym (Nat h) = Nat (R/Nat-sym h)
  A∋ᵒ≐-sym (h₁ × h₂) = A∋≐-sym h₁ × A∋≐-sym h₂
  A∋ᵒ≐-sym (Eq h h≐) = Eq (R/Eq-sym h) h≐

  A∋ᵒ≐-trans (Bool h) (Bool h') = Bool (R/Bool-trans h h')
  A∋ᵒ≐-trans (Nat h) (Nat h') = Nat (R/Nat-trans h h')
  A∋ᵒ≐-trans (h₁ × h₂) (h₁' × h₂') = A∋≐-trans h₁ h₁' × A∋≐-trans h₂ h₂'
  A∋ᵒ≐-trans (Eq h h≐) (Eq h' h≐') = Eq (R/Eq-trans h h') h≐

  A∋ᵒ≐-isPartialEquivalence A = record { sym = A∋ᵒ≐-sym ; trans = A∋ᵒ≐-trans }

  record _∋_≐_ A M M' where
    constructor ⇓_,⇓_,⇓_,_
    pattern
    inductive
    field
      {Aᵒ} : exp
      A⇓Aᵒ : A ⇓ Aᵒ
      {Mᵒ} : exp
      M⇓Mᵒ : M ⇓ Mᵒ
      {M'ᵒ} : exp
      M'⇓M'ᵒ : M' ⇓ M'ᵒ
      Aᵒ∋ᵒMᵒ≐M'ᵒ : Aᵒ ∋ᵒ Mᵒ ≐ M'ᵒ

  _∋_ : (A : exp) → exp → Set
  A ∋ M = A ∋ M ≐ M

  ⇓_,⇓_,⇓-,_ : {A Aᵒ M Mᵒ : exp} (A⇓Aᵒ : A ⇓ Aᵒ) (M⇓Mᵒ : M ⇓ Mᵒ) (Aᵒ∋ᵒMᵒ : Aᵒ ∋ᵒ Mᵒ) → A ∋ M
  ⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓-, Aᵒ∋ᵒMᵒ = ⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M⇓Mᵒ , Aᵒ∋ᵒMᵒ

  A∋≐-sym {A} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ) = ⇓ A⇓Aᵒ ,⇓ M'⇓M'ᵒ ,⇓ M⇓Mᵒ , A∋ᵒ≐-sym A∋ᵒMᵒ≐M'ᵒ

  A∋≐-trans {A} {M₀} {M₁} {M₂} (⇓ A⇓ ,⇓ M₀⇓ ,⇓ M₁⇓ , A∋ᵒMᵒ≐M'ᵒ₁) (⇓ A⇓' ,⇓ M₁⇓' ,⇓ M₂⇓ , A∋ᵒM'ᵒ₁≐M'ᵒ) with ⇓-deterministic A⇓ A⇓' | ⇓-deterministic M₁⇓ M₁⇓'
  ... | refl | refl = ⇓ A⇓ ,⇓ M₀⇓ ,⇓ M₂⇓ , A∋ᵒ≐-trans A∋ᵒMᵒ≐M'ᵒ₁ A∋ᵒM'ᵒ₁≐M'ᵒ

  A∋≐-isPartialEquivalence A = record { sym = A∋≐-sym ; trans = A∋≐-trans }

  -- Lemmas

  lemma/moveᵒ Bool A'∋ᵒM₁≐M₂ = A'∋ᵒM₁≐M₂
  lemma/moveᵒ Nat A'∋ᵒM₁≐M₂ = A'∋ᵒM₁≐M₂
  lemma/moveᵒ (A₁≐A₁'typeᵒ × A₂≐A₂'typeᵒ) (A₁'∋ᵒM₁≐M₁' × A₂'∋ᵒM₂≐M₂') = lemma/move (typeᵒ-type A₁≐A₁'typeᵒ) A₁'∋ᵒM₁≐M₁' × lemma/move (typeᵒ-type A₂≐A₂'typeᵒ) A₂'∋ᵒM₂≐M₂'
  lemma/moveᵒ (Eq A≐A'type A∋M₁≐M₁' A∋M₂≐M₂') (Eq h h≐) = Eq h (A∋≐-trans A∋M₁≐M₁' (A∋≐-trans (lemma/move A≐A'type h≐) (A∋≐-sym A∋M₂≐M₂')))

  lemma/move (⇓ A⇓Aᵒ ,⇓ A'⇓A'ᵒ₁ , Aᵒ≐A'ᵒtypeᵒ) (⇓ A'⇓A'ᵒ ,⇓ M₁⇓M₁ᵒ ,⇓ M₂⇓M₂ᵒ , A'ᵒ∋ᵒM₁ᵒ≐M₂ᵒ) with ⇓-deterministic A'⇓A'ᵒ₁ A'⇓A'ᵒ
  ... | refl = ⇓ A⇓Aᵒ ,⇓ M₁⇓M₁ᵒ ,⇓ M₂⇓M₂ᵒ , lemma/moveᵒ Aᵒ≐A'ᵒtypeᵒ A'ᵒ∋ᵒM₁ᵒ≐M₂ᵒ

  rev-closure-A : {A A' M₁ M₂ : exp} → A ↦ A' → A' ∋ M₁ ≐ M₂ → A ∋ M₁ ≐ M₂
  rev-closure-A A↦A' (⇓ A⇓Aᵒ ,⇓ M₁⇓M₁ᵒ ,⇓ M₂⇓M₂ᵒ , Aᵒ∋ᵒM₁ᵒ≐M₂ᵒ) = ⇓ step⇓ A↦A' A⇓Aᵒ ,⇓ M₁⇓M₁ᵒ ,⇓ M₂⇓M₂ᵒ , Aᵒ∋ᵒM₁ᵒ≐M₂ᵒ

  rev-closure-A* : {A A' M₁ M₂ : exp} → A ↦* A' → A' ∋ M₁ ≐ M₂ → A ∋ M₁ ≐ M₂
  rev-closure-A* here A'∋M₁≐M₂ = A'∋M₁≐M₂
  rev-closure-A* (step A↦A'' A''↦*A') A'∋M₁≐M₂ = rev-closure-A A↦A'' (rev-closure-A* A''↦*A' A'∋M₁≐M₂)

  rev-closure-M : {A M M' : exp} → M ↦ M' → A ∋ M' → A ∋ M
  rev-closure-M M↦M' (⇓ A⇓Aᵒ ,⇓ M'⇓Mᵒ ,⇓ M'⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ) = ⇓ A⇓Aᵒ ,⇓ step⇓ M↦M' M'⇓Mᵒ ,⇓ step⇓ M↦M' M'⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ

  rev-closure-M* : {A M M' : exp} → M ↦* M' → A ∋ M' → A ∋ M
  rev-closure-M* here A∋M' = A∋M'
  rev-closure-M* (step M↦M'' M''↦*M') A∋M' = rev-closure-M M↦M'' (rev-closure-M* M''↦*M' A∋M')

  rev-closure-M*₂ : {A M₁ M₁' M₂ M₂' : exp} → M₁ ↦* M₁' → M₂ ↦* M₂' → A ∋ M₁' ≐ M₂' → A ∋ M₁ ≐ M₂
  rev-closure-M*₂ M₁↦*M₁' M₂↦*M₂' (⇓ A⇓Aᵒ ,⇓ M₁'⇓M₁'ᵒ ,⇓ M₂'⇓M₂'ᵒ , Aᵒ∋ᵒMᵒ≐M'ᵒ) =
    ⇓ A⇓Aᵒ ,⇓ ((↦*-append M₁↦*M₁' (_⇓_.M↦*M' M₁'⇓M₁'ᵒ)) and _⇓_.M'val M₁'⇓M₁'ᵒ) ,⇓ ((↦*-append M₂↦*M₂' (_⇓_.M↦*M' M₂'⇓M₂'ᵒ)) and _⇓_.M'val M₂'⇓M₂'ᵒ) , Aᵒ∋ᵒMᵒ≐M'ᵒ

  -- Hypotheticals

  _>>_ : (A : exp) → (exp → exp → Set) → Set
  A >> J = {a a' : exp} → A ∋ a ≐ a' → J a a'

  _>>_≐_type : (A : exp) (B B' : exp → exp) → Set
  A >> B ≐ B' type = A >> λ a a' → B a ≐ B' a' type

  _>>_type : (A : exp) (B : exp → exp) → Set
  A >> B type = A >> B ≐ B type

  _>>_∋_≐_ : (A : exp) (B N N' : exp → exp) → Set
  A >> B ∋ N ≐ N' = A >> λ a a' → B a ∋ N a ≐ N' a'

  _>>_∋_ : (A : exp) (B N : exp → exp) → Set
  A >> B ∋ N = A >> B ∋ N ≐ N

  -- Facts

  fact/if : {A M M₁ M₀ M₁' M₀' : exp} → Bool ∋ M → A ∋ M₁ → A ∋ M₀ → A ∋ if M M₁ M₀
  fact/if {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Aᵒ∋ᵒMᵒ≐M'ᵒ) h₁ h₀ with val⇓val Bool A⇓Aᵒ
  fact/if {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool (tt Mᵒ⇓tt _)) h₁ h₀ | refl =
    let step-principal M₁ M₀ = lift-principal (λ M → if M M₁ M₀) if/principal (↦*-append (_⇓_.M↦*M' M⇓Mᵒ) (_⇓_.M↦*M' Mᵒ⇓tt)) in
    rev-closure-M* (stepʳ (step-principal M₁ M₀) if/tt) h₁
  fact/if {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool (ff Mᵒ⇓ff _)) h₁ h₀ | refl =
    let step-principal M₁ M₀ = lift-principal (λ M → if M M₁ M₀) if/principal (↦*-append (_⇓_.M↦*M' M⇓Mᵒ) (_⇓_.M↦*M' Mᵒ⇓ff)) in
    rev-closure-M* (stepʳ (step-principal M₁ M₀) if/ff) h₀

  fact/if' : {M A₁ A₀ M₁ M₀ : exp} → Bool ∋ M → A₁ ∋ M₁ → A₀ ∋ M₀ → if M A₁ A₀ ∋ if M M₁ M₀
  fact/if' {A₁ = A₁} {A₀ = A₀} {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Aᵒ∋ᵒMᵒ≐M'ᵒ) h₁ h₀ with val⇓val Bool A⇓Aᵒ
  fact/if' {A₁ = A₁} {A₀ = A₀} {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool (tt Mᵒ⇓tt _)) h₁ h₀ | refl =
    let step-principal M₁ M₀ = lift-principal (λ M → if M M₁ M₀) if/principal (↦*-append (_⇓_.M↦*M' M⇓Mᵒ) (_⇓_.M↦*M' Mᵒ⇓tt)) in
    rev-closure-A* (stepʳ (step-principal A₁ A₀) if/tt) $
    rev-closure-M* (stepʳ (step-principal M₁ M₀) if/tt) $
    h₁
  fact/if' {A₁ = A₁} {A₀ = A₀} {M₁ = M₁} {M₀ = M₀} (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool (ff Mᵒ⇓ff _)) h₁ h₀ | refl =
    let step-principal M₁ M₀ = lift-principal (λ M → if M M₁ M₀) if/principal (↦*-append (_⇓_.M↦*M' M⇓Mᵒ) (_⇓_.M↦*M' Mᵒ⇓ff)) in
    rev-closure-A* (stepʳ (step-principal A₁ A₀) if/ff) $
    rev-closure-M* (stepʳ (step-principal M₁ M₀) if/ff) $
    h₀

  R/Nat⇒Nat∋≐ : {N N' : exp} → R/Nat N N' → Nat ∋ N ≐ N'
  R/Nat⇒Nat∋≐ (zero h h') = ⇓ here and Nat ,⇓ h ,⇓ h' , Nat (zero (here and _⇓_.M'val h) (here and _⇓_.M'val h'))
  R/Nat⇒Nat∋≐ (succ h h' r) = ⇓ here and Nat ,⇓ h ,⇓ h' , Nat (succ (here and _⇓_.M'val h) (here and _⇓_.M'val h') r)

  fact/rec : ∀ {B M₀ M₁ M} →
    Nat >> B type →
    B zero ∋ M₀ →
    Nat >> (λ a a' → B a >> λ b b' → B (succ a) ∋ M₁ a b ≐ M₁ a' b') →
    Nat ∋ M → B M ∋ rec M₀ M₁ M
  fact/rec Nat>>Btype h₀ h₁ (⇓ A⇓Aᵒ ,⇓ M⇓Mᵒ ,⇓ M⇓M'ᵒ , Aᵒ∋ᵒMᵒ≐M'ᵒ) with val⇓val Nat A⇓Aᵒ
  fact/rec {B} {M₀} {M₁} Nat>>Btype h₀ h₁ (⇓ A⇓Nat ,⇓ M⇓Mᵒ ,⇓ M⇓M'ᵒ , Nat r) | refl = induction (_⇓_.M↦*M' M⇓Mᵒ) r
    where
      induction : {M Mᵒ M'ᵒ : exp} → M ↦* Mᵒ → R/Nat Mᵒ M'ᵒ → B M ∋ rec M₀ M₁ M
      induction M↦*Mᵒ (zero Mᵒ⇓zero Mᵒ⇓zero') =
        let step-principal  = lift-principal (rec M₀ M₁) rec/principal (↦*-append M↦*Mᵒ (_⇓_.M↦*M' Mᵒ⇓zero)) in
        rev-closure-M* (stepʳ step-principal rec/zero) $
        lemma/move (Nat>>Btype (⇓ A⇓Nat ,⇓ step*⇓ M↦*Mᵒ Mᵒ⇓zero ,⇓ val⇓ zero , Nat (zero (val⇓ zero) (val⇓ zero)))) $
        h₀
      induction M↦*Mᵒ (succ Mᵒ⇓succN Mᵒ⇓succN' r) =
        let step-principal  = lift-principal (rec M₀ M₁) rec/principal (↦*-append M↦*Mᵒ (_⇓_.M↦*M' Mᵒ⇓succN)) in
        rev-closure-M* (stepʳ step-principal rec/succ) $
        lemma/move (Nat>>Btype (⇓ A⇓Nat ,⇓ step*⇓ M↦*Mᵒ Mᵒ⇓succN ,⇓ val⇓ succ , Nat (succ (val⇓ succ) (val⇓ succ) (per-refl R/Nat-isPartialEquivalence r)))) $
        h₁ (per-refl (A∋≐-isPartialEquivalence Nat) (R/Nat⇒Nat∋≐ r)) (induction here r)

  fact/·1 : {A₁ A₂ M : exp} → A₁ val → A₂ val → (A₁ × A₂) ∋ M → A₁ ∋ (M ·1)
  fact/·1 {A₁ = A₁} A₁val A₂val (⇓ A⇓Aᵒ ,⇓ M⇓⟨M₁,M₂⟩ ,⇓ M⇓⟨M₁',M₂'⟩ , Aᵒ∋ᵒMᵒ≐M'ᵒ) with val⇓val (A₁val × A₂val) A⇓Aᵒ
  fact/·1 {A₁ = A₁} A₁val A₂val (⇓ A⇓Aᵒ ,⇓ M⇓⟨M₁,M₂⟩ ,⇓ M⇓⟨M₁',M₂'⟩ , (A₁∋M₁≐M₁' × A₂∋M₂≐M₂')) | refl =
    rev-closure-M* (stepʳ (lift-principal _·1 _·1/principal (_⇓_.M↦*M' M⇓⟨M₁,M₂⟩)) _·1) (per-refl (A∋≐-isPartialEquivalence A₁) A₁∋M₁≐M₁')

  fact/⟨,⟩·1 : {A₁ M₁ M₂ : exp} → A₁ ∋ M₁ → A₁ ∋ ⟨ M₁ , M₂ ⟩ ·1 ≐ M₁
  fact/⟨,⟩·1 (⇓ A⇓Aᵒ ,⇓ M₁⇓Mᵒ ,⇓ M₁⇓M'ᵒ , A₁∋ᵒMᵒ≐M'ᵒ) = ⇓ A⇓Aᵒ ,⇓ step⇓ _·1 M₁⇓Mᵒ ,⇓ M₁⇓M'ᵒ , A₁∋ᵒMᵒ≐M'ᵒ

  fact/eq/inhabited : Eq Nat (succ zero) (succ zero) ∋ refl
  fact/eq/inhabited =
    ⇓ val⇓ Eq ,⇓ val⇓ refl ,⇓-,
      Eq (refl (val⇓ refl) (val⇓ refl)) (
        ⇓ val⇓ Nat ,⇓ val⇓ succ ,⇓-, (
          Nat (succ (val⇓ succ) (val⇓ succ) (zero (val⇓ zero) (val⇓ zero)))
        )
      )

  fact/eq/reflexive : {A M : exp} → A ∋ M → Eq A M M ∋ refl
  fact/eq/reflexive A∋M = ⇓ val⇓ Eq ,⇓ val⇓ refl ,⇓-, Eq (refl (val⇓ refl) (val⇓ refl)) A∋M
