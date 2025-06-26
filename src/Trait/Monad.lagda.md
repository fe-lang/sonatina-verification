```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Monad where

open import Prim.Type
open import Data.Pi
open import Meta.Idiom


record Monad {u} (M : Type u → Type u) : Typeω where
  -- infixl 1 _>>=_ _>>_ _>=>_
  -- infixr 1 _=<<_ _<=<_
  field
    unitM : {A : Type u} → A → M A
    multM : {A : Type u} → M (M A) → M A

   -- _>>=_  : {A B : Type M.lvl}
   --        → M.₀ A → (A → M.₀ B) → M.₀ B
    -- @0 monad-id : ∀ {u} {A : Type u}
--              → (f : M.₀ A) → (f >>= (λ x → return (id x))) ＝ f
--     @0 monad-comp : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
--                → (f : B → C) (g : A → B) (x : M.₀ A)
--                → (x >>= (λ x₁ → return ((f ∘ g) x₁))) ＝
--                    ((λ x₁ → x₁ >>= (λ x₂ → return (f x₂))) ∘
--                    (λ x₁ → x₁ >>= (λ x₂ → return (g x₂)))) x

--   _>>_ : ∀ {u v} {A : Type u} {B : Type v}
--        → M.₀ A → M.₀ B → M.₀ B
--   m₁ >> m₂ = m₁ >>= λ _ → m₂

--   _=<<_ : ∀ {u v} {A : Type u} {B : Type v}
--         → (A → M.₀ B) → M.₀ A → M.₀ B
--   f =<< c = c >>= f

--   _>=>_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
--         → (A → M.₀ B) → (B → M.₀ C) → (A → M.₀ C)
--   f >=> g = _=<<_ g ∘ f

--   _<=<_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
--         → (B → M.₀ C) → (A → M.₀ B) → (A → M.₀ C)
--   g <=< f = f >=> g

--   join : ∀ {ℓ} {A : Type ℓ} → M.₀ (M.₀ A) → M.₀ A
--   join m = m >>= id

-- --   instance
-- --     Monad-⦃Func⦄ : Func M
-- --     Monad-⦃Func⦄ .Func.fmap-id = monad-id
-- --     Monad-⦃Func⦄ .Func.fmap-comp = monad-comp

-- --   mapM : ∀ {u v} {A : Type u} {B : Type v}
-- --        → (A → M.₀ B) → List A → M.₀ (List B)
-- --   mapM f []       = return []
-- --   mapM f (x ∷ xs) = do y ← f x; (y ∷_) <$> mapM f xs

-- --   -- concatMapM : ∀ {u v} {A : Type u} {B : Type v}
-- --   --            → (A → M (List B)) → List A → M (List B)
-- --   -- concatMapM f xs = concat <$> mapM f xs

-- --   forM : ∀ {u v} {A : Type u} {B : Type v}
-- --        → List A → (A → M.₀ B) → M.₀ (List B)
-- --   forM []       _ = return []
-- --   forM (x ∷ xs) f = do y ← f x; y ∷_ <$> forM xs f

-- --   -- concatForM : ∀ {u v} {A : Type u} {B : Type v}
-- --   --            → List A → (A → M (List B)) → M (List B)
-- --   -- concatForM xs f = concat <$> forM xs f

-- --   return⊤ void : ∀ {u} {A : Type u} → M.₀ A → M.₀ ⊤
-- --   return⊤ k = k >> return tt
-- --   void = return⊤

-- --   -- filterM  : ∀ {u v} {A : Type u} {B : Type v}
-- --   --          → (A → M Bool) → List A → M (List A)
-- --   -- filterM _ [] = return []
-- --   -- filterM p (x ∷ xs) = do
-- --   --   b ← p x
-- --   --   ((if b then [ x ] else []) ++_) <$> filterM p xs

-- --   traverseM : ∀ {u v} {A : Type u} {B : Type v}
-- --             → ⦃ Applicative M ⦄ → ⦃ Monad M ⦄
-- --             → (A → M.₀ B) → List A → M.₀ (List B)
-- --   traverseM f = λ where
-- --     [] → return []
-- --     (x ∷ xs) → ⦇ f x ∷ traverseM f xs ⦈

-- -- open Monad ⦃...⦄ public
