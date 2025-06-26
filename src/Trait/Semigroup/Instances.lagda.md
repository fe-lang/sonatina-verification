```agda
{-# OPTIONS --erased-cubical #-}
module Trait.Semigroup.Instances where

open import Prim.Type
open import Data.Sigma.Type
open import Data.Path.Type

open import Data.List.Type
open import Data.Maybe.Type
open import Data.String.Type

open import Trait.Semigroup.Type

module _ {ℓ} {A : Type ℓ} where
  instance
    -- SemigroupT-List : SemigroupT (List A)
    -- SemigroupT-List ._·_ = _++_
    -- SemigroupT-List ._·_ = _++_

    -- SemigroupT-List⁺ : SemigroupT (List⁺ A)
    -- SemigroupT-List⁺ ._·_ = _⁺++⁺_

    -- SemigroupT-∃Vec : SemigroupT (Σ (Vec A))
    -- SemigroupT-∃Vec ._·_ (_ , v) (_ , v′) = _ , (v V.++ v′)
    --   where import Data.Vec as V

    -- SemigroupT-String : SemigroupT String
    -- SemigroupT-String ._·_ = Str._++_
    --   where import Data.String.Type as Str

    SemigroupT-Maybe : ⦃ SemigroupT A ⦄ → SemigroupT (Maybe A)
    SemigroupT-Maybe ._·_ = λ where
      (just x) (just y) → just (x · y)
      (just x) nothing  → just x
      nothing  m        → m
    SemigroupT-Maybe .sassoc = λ where
      (just _) (just _) (just _) → ap just (sassoc _ _ _)
      (just _) (just _) nothing  → refl
      (just _) nothing  _        → refl
      nothing  (just _) _        → refl
      nothing  nothing  _        → refl
    SemigroupT-Maybe .scomm = λ where
      (just x) (just y) → ap just (scomm x y)
      (just _) nothing  → refl
      nothing  (just _) → refl
      nothing  nothing  → refl

-- ** natural numbers
-- module _ where
--   open import Data.Nat
--   open import Data.Nat.Properties

--   SemigroupT-ℕ-+ = SemigroupT ℕ ∋ λ where ._·_ → _+_
--   SemigroupTLaws-ℕ-+ = SemigroupTLaws ℕ _≡_ ∋
--     record {·-assocʳ = +-assoc; ·-comm = +-comm}
--     where instance _ = SemigroupT-ℕ-+

--   SemigroupT-ℕ-* = SemigroupT ℕ ∋ λ where ._·_ → _*_
--   SemigroupTLaws-ℕ-* = SemigroupTLaws ℕ _≡_ ∋
--     record {·-assocʳ = *-assoc; ·-comm = *-comm}
--     where instance _ = SemigroupT-ℕ-*

-- -- ** binary natural numbers
-- module _ where
--   open import Data.Nat.Binary
--   open import Data.Nat.Binary.Properties

--   SemigroupT-ℕᵇ-+ = SemigroupT ℕᵇ ∋ λ where ._·_ → _+_
--   SemigroupTLaws-ℕᵇ-+ = SemigroupTLaws ℕᵇ _≡_ ∋
--     record {·-assocʳ = +-assoc; ·-comm = +-comm}
--     where instance _ = SemigroupT-ℕᵇ-+

-- -- ** integers
-- module _ where
--   open import Data.Integer
--   open import Data.Integer.Properties

--   SemigroupT-ℤ-+ = SemigroupT ℤ ∋ λ where ._·_ → _+_
--   SemigroupTLaws-ℤ-+ = SemigroupTLaws ℤ _≡_ ∋
--     record {·-assocʳ = +-assoc; ·-comm = +-comm}
--     where instance _ = SemigroupT-ℤ-+

--   SemigroupT-ℤ-* = SemigroupT ℤ ∋ λ where ._·_ → _*_
--   SemigroupTLaws-ℤ-* = SemigroupTLaws ℤ _≡_ ∋
--     record {·-assocʳ = *-assoc; ·-comm = *-comm}
--     where instance _ = SemigroupT-ℤ-*
