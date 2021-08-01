module CTT where

record Language : Set₁ where
  field
    exp : Set
    _val : exp → Set
    _↦_ : exp → exp → Set

    _≐_typeᵒ : exp → exp → Set
    _∋ᵒ_≐_ : exp → exp → exp → Set

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

  record _⇓_ (M M' : exp) : Set where
    field
      M↦*M' : M ↦* M'
      M'val : M' val

  step⇓ : {M M' M'' : exp} → M ↦ M' → M' ⇓ M'' → M ⇓ M''
  step⇓ h record { M↦*M' = M↦*M' ; M'val = M'val } = record { M↦*M' = step h M↦*M' ; M'val = M'val }

module MkType (L : Language) where
  open Language L
  open MultiStep L

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

module MkExp (L : Language) where
  open Language L
  open MultiStep L

  _∋ᵒ_ : (A : exp) → exp → Set
  A ∋ᵒ M = A ∋ᵒ M ≐ M

  record _∋_≐_ (A : exp) (M M' : exp) : Set where
    constructor ⇓_,⇓_,_
    field
      {Mᵒ} : exp
      M⇓Mᵒ : M ⇓ Mᵒ
      {M'ᵒ} : exp
      M'⇓M'ᵒ : M' ⇓ M'ᵒ
      A∋ᵒMᵒ≐M'ᵒ : A ∋ᵒ Mᵒ ≐ M'ᵒ

  _∋_ : (A : exp) → exp → Set
  A ∋ M = A ∋ M ≐ M


  -- Lemmas

  bwd-closure : {A M M' : exp} → M ↦ M' → A ∋ M' → A ∋ M
  bwd-closure M↦M' (⇓ if⇓Mᵒ ,⇓ if⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ) = ⇓ step⇓ M↦M' if⇓Mᵒ ,⇓ step⇓ M↦M' if⇓M'ᵒ , A∋ᵒMᵒ≐M'ᵒ

  bwd-closure* : {A M M' : exp} → M ↦* M' → A ∋ M' → A ∋ M
  bwd-closure* here A∋M' = A∋M'
  bwd-closure* (step M↦M'' M''↦*M') A∋M' = bwd-closure M↦M'' (bwd-closure* M''↦*M' A∋M')

  lift-principal : (f : exp → exp) → ({M M' : exp} → M ↦ M' → f M ↦ f M') → {M M' : exp} → M ↦* M' → f M ↦* f M'
  lift-principal f h here = here
  lift-principal f h (step M↦M'' M''↦*M') = step (h M↦M'') (lift-principal f h M''↦*M')


module Example1 where
  data exp : Set where
    Bool : exp
    tt ff : exp
    if : exp → exp → exp → exp

  data _val : exp → Set where
    Bool : Bool val
    tt : tt val
    ff : ff val

  data _↦_ : exp → exp → Set where
    if/principal : {M M' M₁ M₀ : exp} → M ↦ M' → if M M₁ M₀ ↦ if M' M₁ M₀
    if/tt : (M₁ M₀ : exp) → if tt M₁ M₀ ↦ M₁
    if/ff : (M₁ M₀ : exp) → if ff M₁ M₀ ↦ M₀

  data _≐_typeᵒ : exp → exp → Set where
    Bool : Bool ≐ Bool typeᵒ

  data R/Bool : exp → exp → Set where
    tt : R/Bool tt tt
    ff : R/Bool ff ff

  data _∋ᵒ_≐_ : (A : exp) → exp → exp → Set where
    Bool : {M M' : exp} → R/Bool M M' → Bool ∋ᵒ M ≐ M'

  L : Language
  L =
    record
      { exp = exp
      ; _val = _val
      ; _↦_ = _↦_
      ; _≐_typeᵒ = _≐_typeᵒ
      ; _∋ᵒ_≐_ = _∋ᵒ_≐_
      }

  open MultiStep L
  open MkType L
  open MkExp L


  -- Facts

  fact : {A M M₁ M₀ M₁' M₀' : exp} → Bool ∋ M → A ∋ M₁ → A ∋ M₀ → A ∋ if M M₁ M₀
  fact {M₁ = M₁} {M₀ = M₀} (⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool tt) h₁ h₀ = bwd-closure* (stepʳ (lift-principal (λ M → if M M₁ M₀) if/principal (_⇓_.M↦*M' M'⇓M'ᵒ)) (if/tt M₁ M₀)) h₁
  fact {M₁ = M₁} {M₀ = M₀} (⇓ M⇓Mᵒ ,⇓ M'⇓M'ᵒ , Bool ff) h₁ h₀ = bwd-closure* (stepʳ (lift-principal (λ M → if M M₁ M₀) if/principal (_⇓_.M↦*M' M'⇓M'ᵒ)) (if/ff M₁ M₀)) h₀
