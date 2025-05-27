```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Arrow where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Data.Path.Type using (_＝_; refl; sym; ap)
open import Data.Sigma.Type
open import Trait.Category
open import Meta.Idiom
open import Meta.Bind
open import Meta.Invariant

record Quiver : Typeω where
  constructor quiver
  field
    {ℓ-hom} : Level → Level → Level
    Hom : ∀ {s t} → Type s → Type t → Type (ℓ-hom s t)

record Cat (C : Quiver) : Typeω where
  private module C = Quiver C
  field
    seq : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → C.Hom A B → C.Hom B C → C.Hom A C
    is-cat : ∀ {u} → is-category (C.Hom {u} {u}) seq
    assoc : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
          → (f : C.Hom A B) (g : C.Hom B C) (h : C.Hom C D)
          → seq f (seq g h) ＝ seq (seq f g) h

  private
    idn' : ∀ {ℓ} {A : Type ℓ} → C.Hom A A
    idn' {A} = has-identity.idn (is-cat A)

  module _ {u} where
    open is-category (C.Hom {u}) seq is-cat
      (λ f → assoc idn' idn' f) (λ f → sym (assoc f idn' idn')) public

record Arrow (M : Quiver) : Typeω where
  private module M = Quiver M renaming (Hom to infix 2 _↦_)
  infixr 40 _>>>_
  field
    arr : ∀ {s t} {A : Type s} {B : Type t}
        → (A → B) → A M.↦ B
    _>>>_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → A M.↦ B → B M.↦ C → A M.↦ C
    first : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
          → A M.↦ B → A × C M.↦ B × C
    @0 arrow-assoc : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w}
                   → {D : Type z}(f : A M.↦ B) (g : B M.↦ C) (h : C M.↦ D)
                   → f >>> (g >>> h) ＝ (f >>> g) >>> h

  second : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
         → A M.↦ B → C × A M.↦ C × B
  second f = arr swap >>> first f >>> arr swap

open Arrow ⦃ ... ⦄ public

module _ ⦃ M : Quiver ⦄ ⦃ _ : Arrow M ⦄ where
  open Quiver M renaming (Hom to infix 2 _↦_)
  _***_ : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
        → (A ↦ B) → (C ↦ D) → A × C ↦ B × D
  f *** g = first f >>> second g

  _&&&_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → (A ↦ B) → (A ↦ C) → A ↦ B × C
  f &&& g = arr diag >>> (f *** g)

  liftA2 : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
         → (A → B → C) → D ↦ A → D ↦ B → D ↦ C
  liftA2 op f g = (f &&& g) >>> arr λ (b , c) → op b c

  returnA : ∀ {u} → {A : Type u} → A ↦ A
  returnA = arr id

  _^>>_ proc-syntax : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → (A → B) → B ↦ C → A ↦ C
  _^>>_ f a = arr f >>> a
  proc-syntax = _^>>_
  syntax proc-syntax (λ p → e₂) e₁ = proc p ⟶ e₁ ≺ e₂

  _>>^_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → A ↦ B → (B → C) → A ↦ C
  _>>^_ a f = a >>> arr f

  _^<<_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → (B → C) → A ↦ B → A ↦ C
  _^<<_ f a = a >>> arr f

  _<<^_ : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
        → B ↦ C → (A → B) → A ↦ C
  _<<^_ a f = arr f >>> a

instance
  Arrow-Fun : Arrow (quiver λ A B → A → B)
  Arrow-Fun .Arrow.arr = id
  Arrow-Fun .Arrow._>>>_ f g = g ∘ f
  Arrow-Fun .Arrow.first f s = f (s .fst) , s .snd
  Arrow-Fun .Arrow.arrow-assoc f g h = refl
  {-# INCOHERENT Arrow-Fun #-}

  Arrow-Par : ∀ {ℓ} {S : Type ℓ} → Arrow (quiver λ A B → (S → A) → S → B)
  Arrow-Par .Arrow.arr f h s = f (h s)
  Arrow-Par .Arrow._>>>_ m n f s = n (m f) s
  Arrow-Par .Arrow.first m n s = m (λ t → n t .fst) s , n s .snd
  Arrow-Par .Arrow.arrow-assoc f g h = refl

  Arrow-Idiom : {M : Effect} → ⦃ Map M ⦄ → ⦃ Monoidal M ⦄
              → (let module M = Effect M)
              → Arrow (quiver λ A B → M.₀ A → M.₀ B)
  Arrow-Idiom  .Arrow.arr = map
  Arrow-Idiom .Arrow._>>>_ f g = g ∘ f
  Arrow-Idiom .Arrow.first f g = f (map fst g) <,> map snd g
  Arrow-Idiom .Arrow.arrow-assoc f g h = refl
