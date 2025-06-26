```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Product where

open import Prim.Prelude
open import Data.Path.Type
open import Data.Category.Type
open import Trait.Equiv
open import Trait.HLevel

_×cat_ : ∀ {o₁ h₁ o₂ h₂} → Category o₁ h₁ → Category o₂ h₂ → Category {!!} {!!}
_×cat_ {o₁} {h₁} {o₂} {h₂} C D = {!!} module ×cat where
  private
    module C = Category C
    module D = Category D

  ob : Type (o₁ ⊔ o₂)
  ob = C.Ob × D.Ob

  hom : ob → ob → Type (h₁ ⊔ h₂)
  hom (a , a') (b , b') = C.Hom a b × D.Hom a' b'

  prod-seq : {x y z : ob} → hom x y → hom y z → hom x z 
  prod-seq (f , f') (g , g') = f ∙ g , f' ∙ g'

  prod-idn : ∀ x → hom x x
  prod-idn (x , x') = C.idn x , D.idn x'

  private
    pre : {x y : ob} → hom x y → hom x y
    pre {x} f = prod-seq (prod-idn x) f

    post : {x y : ob} → hom x y → hom x y
    post {y} f = prod-seq f (prod-idn y)

    module secC {x y} = is-equiv (C.idn-sec x y)
    module retrC {x y} = is-equiv (C.idn-retr x y)
    module secD {x y} = is-equiv (D.idn-sec x y)
    module retrD {x y} = is-equiv (D.idn-retr x y)

  idn-lequiv : (x y : ob) → is-equiv pre
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .ctr .fst .fst =
    secC.center f .fst
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .ctr .fst .snd =
    secD.center f' .fst
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .ctr .snd i .fst =
    secC.fibers (contr-map (C.idn-sec x y) f .ctr) i .snd i
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .ctr .snd i .snd =
    secD.fibers (contr-map (D.idn-sec x' y') f' .ctr) i .snd i
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .paths (fb₁ , fb₂) i .fst .fst =
    {!!}
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .paths (fb₁ , fb₂) i .fst .snd =
    {!!}
  idn-lequiv (x , x') (y , y') .contr-map (f , f') .paths (fb₁ , fb₂) i .snd j =
    {!!}

  idn-requiv : (x y : ob) → is-equiv post
  idn-requiv (x , x') (y , y') .contr-map f .ctr = {!!}
  idn-requiv (x , x') (y , y') .contr-map f .paths = {!!}

  cons : Category _ _
  cons .Ob = ob
  cons .Hom = hom
  cons .seq = prod-seq
  cons .assoc (f , f') (g , g') (h , h') i =
    C.assoc f g h i , D.assoc f' g' h' i
  cons .is-cat (x , x') .has-identity.idn = prod-idn (x , x')
  cons .is-cat (x , x') .has-identity.idn-idpt i =
    (C.idn-idpt x i) , D.idn-idpt x' i
  cons .is-cat (x , x') .has-identity.idn-sec = idn-lequiv (x , x')
  cons .is-cat (x , x') .has-identity.idn-retr = idn-requiv (x , x')

```
