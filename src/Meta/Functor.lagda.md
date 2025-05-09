
```agda

{-# OPTIONS --safe --erased-cubical #-}
module Control.Functor where

open import Prim.Type
open import Control.Effect
open import Data.Category
open import Data.Category.Functor
open import Lib.Path

Typω : Typeω
Typω = ∀ {o} → Type o → Category o o

Grpdω : Typω
Grpdω A .Category.base .Semicategory.Ob = A
Grpdω A .Category.base .Semicategory.Hom = _＝_
Grpdω A .Category.base .Semicategory._⨾_ = _∙_
Grpdω A .Category.base .Semicategory.assoc = {!!}
Grpdω A .Category.is-cat = {!!}

--Grpdω : Catω

-- module _ ⦃ _ : Comp C ⦄ ⦃ _ : Comp D ⦄ where
--   record Semifunctorial (F : QFunctor) : Typeω where
--     no-eta-equality
--     open QFunctor F
--     field pres-∙ : {ℓx ℓy ℓz : Level} {x : C.Ob ℓx} {y : C.Ob ℓy} {z : C.Ob ℓz}
--                    (f : C.Hom x y) (g : C.Hom y z)
--                  → F₁ (f ∙ g) ＝ F₁ f ∙ F₁ g
