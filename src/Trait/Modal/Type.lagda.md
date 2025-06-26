```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Modal.Type where

open import Prim.Prelude
open import Trait.HLevel.Base
open import Meta.Idiom

record Modality ℓ : Type (ℓ ₊) where
  field
    is-modal : Type ℓ → Type ℓ
    is-prop-is-modal : {A : Type ℓ} → is-prop (is-modal A)

    ◯ : Type ℓ → Type ℓ                                  -- \ci5
    ◯-is-modal : {A : Type ℓ} → is-modal (◯ A)

    η : {A : Type ℓ} → A → ◯ A

    ◯-elim : {A : Type ℓ} {B : ◯ A → Type ℓ}
      (B-modal : (x : ◯ A) → is-modal (B x))
      → ((x : A) → (B (η x))) → ((x : ◯ A) → B x)

    ◯-elim-β : {A : Type ℓ} {B : ◯ A → Type ℓ}
      (B-modal : (x : ◯ A) → is-modal (B x)) (f : (x : A) → (B (η x)))
      → (a : A) → ◯-elim B-modal f (η a) ＝ f a

    ◯-=-is-modal : {A : Type ℓ} (x y : ◯ A) → is-modal (x ＝ y)

open Modality ⦃ ... ⦄ public

module ◯-elim {ℓ} ⦃ M : Modality ℓ ⦄
  (let module M = Modality M)
  {A : Type ℓ} {B : M.◯ A → Type ℓ}
  (B-modal : (x : M.◯ A) → M.is-modal (B x)) (η* : (x : A) → (B (M.η x)))
  where

  f : (x : M.◯ A) → B x
  f = M.◯-elim B-modal η*

  η-β : (a : A) → M.◯-elim B-modal η* (M.η a) ＝ η* a
  η-β = M.◯-elim-β B-modal η*

module ◯-rec {ℓ} ⦃ M : Modality ℓ ⦄ {A : Type ℓ} {B : Type ℓ}
       (let module M = Modality M)
       (B-modal : M.is-modal B) (η* : A → B)
    = ◯-elim (λ _ → B-modal) η*

◯-rec = ◯-rec.f
◯-rec-β = ◯-rec.η-β

{- functoriality -}

module ◯-fmap {ℓ} ⦃ M : Modality ℓ ⦄
  (let module M = Modality M)
  {A B : Type ℓ} (f : A → B) =
    ◯-rec M.◯-is-modal (M.η ∘ f)

◯-map = ◯-fmap.f
◯-map-β = ◯-fmap.η-β

◯-preservesEquiv : ∀ {ℓ} ⦃ M : Modality ℓ ⦄ {A B : Type ℓ} (f : A → B)
                 → is-equiv f → is-equiv (◯-map f)
◯-preservesEquiv f f-ise = equiv (◯-map f) (◯-map e.inv) from-to to-from where
  module e = is-equiv f-ise
  to-from : ∀ ◯b → ◯-map f (◯-map e.inv ◯b) ＝ ◯b
  to-from = ◯-elim
    (λ ◯b → ◯-=-is-modal (◯-map f (◯-map e.inv ◯b)) ◯b)
    (λ b → ap (◯-map f) (◯-map-β e.inv b) ∙ ◯-map-β f (e.inv b) ∙ ap η (e.retr b))
  from-to : ∀ ◯a → ◯-map e.inv (◯-map f ◯a) ＝ ◯a
  from-to = ◯-elim
      (λ ◯a → ◯-=-is-modal (◯-map e.inv (◯-map f ◯a)) ◯a)
      (λ a → ap (◯-map e.inv) (◯-map-β f a) ∙ ◯-map-β e.inv (f a) ∙ ap η (e.sec a))


Modal : (∀ {ℓ} → Modality ℓ) → Effect
Modal M = eff M.◯ where module M {ℓ} = Modality (M {ℓ})

instance
  Map-Modality : ⦃ M : ∀ {ℓ} → Modality ℓ ⦄ → Map (Modal M)
  Map-Modality .Map.map = {!!}

-- ◯-Types : Type (ℓ-suc ℓ)
-- ◯-Types = TypeWithStr ℓ is-modal
