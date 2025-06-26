Following Petrakis' development in "A Yoneda lemma-formulation of the
univalence axiom"

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Univalence where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Data.Pi
open import Data.Path.Type
open import Data.Sigma.Type
open import Trait.Equiv

-- The Yoneda embedding functor
𝓨-path : ∀ {u} {A : Type u} → A → A → Type u
𝓨-path a x = x ＝ a

-- Theorem 1
-- module _ {u v} {A : Type u} (P : A → Type v) (a : A) where
--   𝓨₌-to : 𝓨 a ~> P → P a
--   𝓨₌-to F = F a refl

--   𝓨₌-from : P a → 𝓨 a ~> P
--   𝓨₌-from u x p = transport (λ i → P (p (~ i))) u

--   𝓨-equiv : (𝓨 a ~> P) ≃ P a
--   𝓨-equiv .fst = 𝓨-to
--   𝓨-equiv .snd = equiv 𝓨-to 𝓨-from {!!} {!!}

-- Definition 1

--module _ {u} {A B : Type u} (e : A ≃ B) where

𝓨 : ∀ {u} → Type u → Type u → Type u
𝓨 A X = X ≃ A

module _ {u}  where
  𝓨-refl : {A : Type u} → 𝓨 A A
  𝓨-refl = {!!}
  𝓨eqv : {A B : Type u} (e : A ≃ B) → 𝓨 A ~> 𝓨 B
  𝓨eqv e X e' = eqv-concat e' e

  𝓨-homomorphism : {A B C : Type u} (e : A ≃ B)
                 → (ε : B ≃ C)
                 → 𝓨eqv (eqv-concat e ε) {!!} {!!}
                 ＝ eqv-concat (𝓨eqv e {!!} {!e!}) (𝓨eqv ε {!!} {!!})
  𝓨-homomorphism e ε i = eqv-concat {!!} {!ε!}




  

-- 𝓨-eqv : ∀ {u} {A B : Type u} → A ≃ B → 𝓨 A ~> 𝓨 B
-- 𝓨-eqv e X d = eqv-concat d e

-- 𝓨-homomorphism : ∀ {u} {A B C : Type u}
--                → (e : A ≃ B) (ε : B ≃ C)
--                → 𝓨-eqv (eqv-concat e ε) ＝ {!!}
-- 𝓨-homomorphism = {!!}

-- module weak-ua {u} (P : Type u → Type u) (A : Type u) where
--   to : (𝓨 A ~> P) → P A
--   to y = y A (id , id-equiv)

--   from : P A → 𝓨 A ~> P
--   from σ X e = {!!}

--   P-equiv : (𝓨 A ~> P) ≃ P A
--   P-equiv .fst = to
--   P-equiv .snd = equiv to from {!!} {!!}
--   -- to : P A → (X : Type u) → X ≃ A → P X
--   -- to u X (e , is-eq) = {!!}

--   --ua' : (X : Type u) →
