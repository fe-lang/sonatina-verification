```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Meta where

open import Prim.Type

open import Prim.Path
open import Lib.Path.Comp
open import Lib.Path.Groupoid
open import Lib.Path.Square
open import Prim.Equiv

open import Data.Category.Type
open import Data.Semicategory.Axioms
open import Data.Semicategory.Meta
open import Data.Semicategory.Iso

module S {u} = Semicategory (ωSemigrpd u)

refl-is-lequiv : ∀ {ℓ} (A B : Type ℓ) → is-equiv (λ (p : A ＝ B) → refl ∙ p)
refl-is-lequiv A B .eq-inv = id
refl-is-lequiv A B .eq-sec = idnl-path
refl-is-lequiv A B .eq-retr = idnl-path
```
Goal: Type ℓ
———— Boundary (wanted) —————————————————————————————————————
k = i0 ⊢ A
k = i1 ⊢ B
j = i0 ⊢ Agda.Primitive.Cubical.primHComp
         (λ j₁ .o → path-faces refl refl (refl ∙ p) k j₁ _) (refl k)
j = i1 ⊢ Agda.Primitive.Cubical.primHComp
         (λ j₁ .o → path-faces refl refl p k j₁ _) (refl k)
i = i0 ⊢ Agda.Primitive.Cubical.primHComp
         (λ j₁ .o → path-faces refl refl (idnl-path p j) k j₁ _) (refl k)
i = i1 ⊢ Agda.Primitive.Cubical.primHComp
         (λ j₁ .o →
            (λ { i₁ (k = i0) → A
               ; i₁ (k = i1) → (refl ∙ p) (j ∨ i₁)
               ; i₁ (j = i1) → (refl ∙ p) k
               ; i₁ (i₁ = i0) → (refl ∙ p) (j ∧ k)
               })
            j₁ _)
         ((refl ∙ p) (j ∧ k))
————————————————————————————————————————————————————————————
```
refl-is-lequiv {ℓ} A B .eq-adj p i j k =
  let
    idpt : refl ∙ refl ＝ erefl A
    idpt = idpt-path A

    path1 : PathP (λ i₁ → refl i₁ ＝ (refl ⌞ refl ⌟ (refl ∙ p)) i₁) refl
             (refl ∙ p)
    path1 = path-fill refl refl (refl ∙ p)
  in hcomp (∂ i ∨ ∂ j ∨ ∂ k) λ where
    l (i = i0) → {!!}
    l (i = i1) → {!!}
    l (j = i0) → {!!}
    l (j = i1) → {!!}
    l (k = i0) → {!!}
    l (k = i1) → {!!}
    l (l = i0) → {!!}



    
refl-iso : ∀ {ℓ} (A : Type ℓ)
         → is-iso (ωSemigrpd ℓ) (refl)
refl-iso A .iso-invl B = refl-is-lequiv A B
refl-iso A .iso-invr w = {!!}

ωGrpd : ∀ u → Category (u ₊) (u ₊)
ωGrpd u .Category.base = ωSemigrpd u
ωGrpd u .Category.is-cat A .Data.Semicategory.Axioms.has-identity.idn = refl
ωGrpd u .Category.is-cat A .Data.Semicategory.Axioms.has-identity.idpt = idpt-path A
ωGrpd u .Category.is-cat A .has-identity.iso = refl-iso A
```
