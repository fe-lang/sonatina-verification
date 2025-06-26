```agda
{-# OPTIONS --safe --erased-cubical #-}

open import Meta.Object
module Trait.Equiv.Identity {O : Object} (C : Composable O) where

open import Prim.Type
open import Prim.Kan
open import Prim.Interval
open import Data.Sigma.Type
open import Data.Path

open import Trait.Contr
open import Trait.HLevel.Base
open import Trait.Equiv
open import Trait.Embedding
open import Data.Pi

infix 2 _≅_

private module C where
  open Object O public
  open Composable C public

is-idempotent : ∀ {x} (i : C.₁ x x) → Type C.ℓ₁
is-idempotent i = i ∙ i ＝ i

record is-iso {x y} (f : C.₁ x y) : Type C.ℓ where
  field
    pre : (z : C.₀) → is-equiv (λ (g : C.₁ y z) → f ∙ g)
    post  : (w : C.₀) → is-equiv (λ (h : C.₁ w x) → h ∙ f)

  linv : ∀ {z} → C.₁ x z → C.₁ y z
  linv {z} = eqv-inv (pre z)

  rinv : ∀ {w} → C.₁ w y → C.₁ w x
  rinv {w} = eqv-inv (post w)

  lunit : C.₁ x x
  lunit = rinv f

  runit : C.₁ y y
  runit = linv f

_≅_ : C.₀ → C.₀ → Type C.ℓ
x ≅ y = Σ f ∶ C.₁ x y , is-iso f


```

Re: John Chen's Semicategories with Identities literate agda
development, "The type of identifications of an equivalence f with ℐ f
is equivalent to the type of witnesses of idempotence of f."

```

has-iso-lcoh : ∀ {x} {f : C.₁ x x} → is-iso f → Type C.ℓ₁
has-iso-lcoh {f} iso = is-iso.lunit iso ＝ f

has-iso-rcoh : ∀ {x} {f : C.₁ x x} → is-iso f → Type C.ℓ₁
has-iso-rcoh {f} iso = is-iso.runit iso ＝ f

has-lunit-coh : ∀ {x} (i : C.₁ x x) → Type C.ℓ
has-lunit-coh {x} i = ∀ {y} (f : C.₁ x y) → i ∙ (i ∙ f) ＝ i ∙ f

has-runit-coh : ∀ {x} (i : C.₁ x x) → Type C.ℓ
has-runit-coh {x} i = ∀ {w} (f : C.₁ w x) → (f ∙ i) ∙ i ＝ f ∙ i

module idn-laws {x} {idn : C.₁ x x}
  (e : is-iso idn)
  (idem : is-idempotent idn)
  where
  module _ {y : C.₀} (f : C.₁ x y) where
    private
      einv = is-iso.pre e y
      linv = eqv-inv einv
      unit = eqv-sec einv

    lneutral : has-lunit-coh idn → idn ∙ f ＝ f
    lneutral coh i = hcomp (∂ i) λ where
      k (i = i0) → unit (idn ∙ f) k
      k (i = i1) → unit f k
      k (k = i0) → linv (coh f i)

  module _ {w : C.₀} (f : C.₁ w x) where
    private
      einv = is-iso.post e w
      rinv = eqv-inv einv
      unit = eqv-sec einv
    rneutral : has-runit-coh idn → f ∙ idn ＝ f
    rneutral coh i = hcomp (∂ i) λ where
      k (i = i0) → unit (f ∙ idn) k
      k (i = i1) → unit f k
      k (k = i0) → rinv (coh f i)

module idem-equiv→coh {x} {idn : C.₁ x x}
  (e : is-iso idn)
  (idem : is-idempotent idn)
  where

  c0 : fiber (_∙_ idn) idn
  c0 = contr-map (is-iso.pre e x) idn .ctr

  c1 : fiber (_∙ idn) idn
  c1 = contr-map (is-iso.post e x) idn .ctr

  h0 : C.₁ x x
  h0 = c0 .fst

  p0 : idn ∙ h0 ＝ idn
  p0 = c0 .snd

  h1 : C.₁ x x
  h1 = c1 .fst

  p1 : h1 ∙ idn ＝ idn
  p1 = c1 .snd

  f0 : Path (fiber (idn ∙_) idn) (h0 , p0) (idn , idem)
  f0 = is-equiv.fibers (is-iso.pre e x) (idn , idem)

  f1 : Path (fiber (_∙ idn) idn) (h1 , p1) (idn , idem)
  f1 = is-equiv.fibers (is-iso.post e x) (idn , idem)

  α0 : h0 ＝ idn
  α0 = ap fst f0

  α1 : h1 ＝ idn
  α1 = ap fst f1

  has-rcoh : has-iso-rcoh e
  has-rcoh = α0

  has-lcoh : has-iso-lcoh e
  has-lcoh = α1

record is-idem-equiv {x} (idn : C.₁ x x) : Type C.ℓ where
  field
    idem : is-idempotent idn
    iso : is-iso idn

record is-coherent-unit {x} (idn : C.₁ x x) : Type C.ℓ where
  field
    iso : is-iso idn
    lcoh : has-iso-lcoh iso
    rcoh : has-iso-lcoh iso

module _ {x} {idn idn' : C.₁ x x}
  (e : is-idem-equiv idn)
  (e' : is-idem-equiv idn')
  (lunit-coh : has-lunit-coh idn)
  (runit-coh : has-runit-coh idn')
  where
  module lcoh = idem-equiv→coh (is-idem-equiv.iso e) (e .is-idem-equiv.idem)
  module rcoh = idem-equiv→coh (is-idem-equiv.iso e') (e' .is-idem-equiv.idem)
  private
    rneutral' = idn-laws.rneutral
      (e' .is-idem-equiv.iso) (e' .is-idem-equiv.idem) idn runit-coh

    lneutral = idn-laws.lneutral
      (e .is-idem-equiv.iso) (e .is-idem-equiv.idem) idn' lunit-coh

  idem-equiv→contr-idn : idn ＝ idn'
  idem-equiv→contr-idn = sym rneutral' ∙ lneutral

  --idem-equiv→contr-idem : idn

module _ {x} {idn : C.₁ x x} (e : is-iso idn)
  (lcoh : has-iso-lcoh e)
  (rcoh : has-iso-rcoh e)
  where
  private
    module fibers
      (e : is-iso idn)
      (lcoh : has-iso-lcoh e)
      (rcoh : has-iso-rcoh e)
      where
      open is-iso e
      E = C.₁ x x
      lctr : (i : E) → fiber (idn ∙_) i
      lctr = is-equiv.center (pre x)

      rctr : (i : E) → fiber (_∙ idn) i
      rctr = is-equiv.center (post x)

      lpre : linv (idn ∙ idn) ＝ idn
      lpre = eqv-sec (pre x) idn

      rpre : idn ∙ runit ＝ idn
      rpre = eqv-retr (pre x) idn

      lpost : lunit ∙ idn ＝ idn
      lpost = eqv-retr (post x) idn

      w0 : idn ∙ idn ＝ idn
      w0 = ap (idn ∙_) (sym rcoh) ∙ rpre

      w1 : idn ∙ idn ＝ idn
      w1 = ap (_∙ idn) (sym lcoh) ∙ lpost

      w : idn ∙ idn ＝ idn ∙ idn
      w = w0 ∙ sym w1

      ι : Square w0 w w1 refl
      ι = cone w0 w1

      ψ : Path (fiber id idn) (idn ∙ idn , w0) (idn ∙ idn , w1)
      ψ i = w i , λ j → ι i j

      κ : idn ∙ idn ＝ idn
      κ i = ψ i .snd i

      idn-equiv : is-idem-equiv idn
      idn-equiv .is-idem-equiv.idem = κ
      idn-equiv .is-idem-equiv.iso .is-iso.pre = pre
      idn-equiv .is-idem-equiv.iso .is-iso.post = post

    idn-equiv : is-idem-equiv idn
    idn-equiv = fibers.idn-equiv e lcoh rcoh

    contr : is-contr (is-idem-equiv idn)
    contr .ctr = idn-equiv
    contr .paths e' i .is-idem-equiv.idem j = {!!}
    contr .paths e' i .is-idem-equiv.iso = {!!}


    -- private module fibers (h : E) where
    --   c0 : E
    --   c0 = lctr (idn ∙ h) .fst

    --   c1 : E
    --   c1 = rctr (h ∙ idn) .fst

    --   α0 : idn ∙ c0 ＝ idn ∙ h
    --   α0 = lctr (idn ∙ h) .snd

    --   α1 : c1 ∙ idn ＝ h ∙ idn
    --   α1 = rctr (h ∙ idn) .snd

    --   lpaths : c0 , α0 ＝ h , erefl (idn ∙ h)
    --   lpaths = is-equiv.fibers (pre x) (h , refl)

    --   rpaths : c1 , α1 ＝ h , erefl (h ∙ idn)
    --   rpaths = is-equiv.fibers (post x) (h , refl)

    --   η : c0 ＝ h
    --   η = ap fst lpaths

    --   ε : c1 ＝ h
    --   ε = ap fst rpaths

    --   ω : c0 ＝ c1
    --   ω = η ∙ sym ε

    --   θ : Square η ω ε refl
    --   θ = cone η ε

    --   τ : Path (fiber id h) (c0 , η) (c1 , ε)
    --   τ i = ω i , λ j → θ i j

  -- private module _ {h : E} ((k , q) : fiber id h) (p : h ＝ k)  where
  --   module F = fibers idn
  --   open F using (c0; c1)

  --   ρ : Path (fiber id idn) (c0 , lpre) (c1 , lpost)
  --   ρ = F.τ

  --   α : c0 ＝ c1
  --   α = ap fst ρ

  --   γ : Path (fiber id h) (h , refl) (k , q)
  --   γ i = p i , λ j → hcomp (∂ j ∨ ∂ i) λ where
  --     k (j = i0) → p (i ∧ k)
  --     k (k = i0) → {!!}
  --     k (j = i1) → q (i ∨ k)
  --     k (i = i0) → {!q (i ∨ ~ k)!}
  --     k (i = i1) → {!!}


  -- v : idn ∙ runit ＝ lunit ∙ idn
  -- v = rpre ∙ sym rpost

  -- ξ : Square rpre v rpost refl
  -- ξ = cone rpre rpost

  -- χ0 : Path (fiber id (idn ∙ idn)) (idn ∙ c0 idn , α0 idn) (c1 idn ∙ idn , α1 idn)
  -- χ0 i = u i , λ j → ζ i j

  -- χ1 : Path (fiber id idn) (idn ∙ runit , rpre) (lunit ∙ idn , rpost)
  -- χ1 i = v i , λ j → ξ i j

  σ0 : {!!}
  σ0 = {!!}

  σ1 : {!!}
  σ1 = {!!}

  -- r0 : Square refl w0 (sym q1) (ap (_∙ idn) (sym lcoh))
  -- r0 = {!!}

  -- r1 : Square (ap (idn ∙_) (sym a0)) refl w0 q0
  -- r1 = {!!}

  -- δ : Square
  --     q0
  --     (ap2 _∙_ (sym a1) a0)
  --     q1
  --     refl
  -- δ i j = hcomp (∂ i ∨ ∂ j) λ where
  --    k (k = i0) → {!? ∙ ?!}
  --    k (i = i0) → {!!}
  --    k (j = i0) → sym a1 i ∙ a0 i
  --    k (i = i1) → {!!}
  --    k (j = i1) → {!!}

  -- r : Square (ap (idn ∙_) (sym rcoh)) refl (ap (_∙ idn) (sym lcoh)) (q0 ∙ sym q1)
  -- r i j = hcomp (∂ i ∨ ~ j) λ where
  --   k (i = i0) → idn ∙ φ k (~ j)
  --   k (j = i0) → w0 (i ∧ j)
  --   k (i = i1) → r0 j k
  --   k (k = i0) → r1 i j


  -- l : w0 ＝ w1
  -- l i j = hcomp (∂ j) λ where
  --   k (j = i0) → idn ∙ idn
  --   k (k = i0) → r i j
  --   k (j = i1) → q i k

  -- cb : Square (ap (idn ∙_) a0) (rpre ∙ sym rpost) (ap (_∙ idn) a1) refl
  -- cb i j = hcomp (∂ i ∨ ∂ j) λ where
  --   k (i = i0) → s0 j (~ k)
  --   k (j = i0) → q i (~ k)
  --   k (i = i1) → s1 j (~ k)
  --   k (k = i0) → idn
  --   k (j = i1) → l i (~ k)

  -- σ : SquareP (λ i j → sym-square refl (sym a1) i j ∙ a0 (i ∨ j) ＝ idn)
  --     s0 δ s1 l
  -- σ = {!!}


  -- fin : (i : I) → w0 , refl ＝ w1 , refl
  -- fin φ i = (l i) , λ j → cb i j


  --module _

  --     p : (f ∙ idn) ∙ idn ＝ f ∙ idn
  --     p = sym (rassoc f) ∙ ap (f ∙_) idem

  -- has-idem-rcoh : ∀ {w} (f : C.₁ w x) → f ∙ (idn ∙ idn) ＝ f ∙ idn → Type C.ℓ₁
  -- has-idem-rcoh f p = ap (idn ∙_) (rneutral f) ＝ p


-- is-category : Type C.ℓ
-- is-category = ∀ x → is-idem-equiv x

-- module is-category (is-cat : is-category)
--   (let module M {x} = is-idem-equiv (is-cat x))
--   where
--   open M
--   module _ {x y : C.₀} where
--     epre = M.sec {x} y
--     linv = eqv-inv epre
--     inv-pre : is-equiv linv
--     inv-pre = Equiv.inverse (idn ∙_ , epre) .snd

--     epost = M.retr {y} x
--     rinv = eqv-inv epost

--     inv-post : is-equiv rinv
--     inv-post = Equiv.inverse (_∙ idn , epost) .snd

--     lctr : (f : C.₁ x y) → fiber (idn ∙_) f
--     lctr = is-equiv.center epre

--     rctr : (f : C.₁ x y) → fiber (_∙ idn) f
--     rctr = is-equiv.center epost

--     lunit : (f : C.₁ x y) → linv (idn ∙ f) ＝ f
--     lunit = is-equiv.sec epre

--     lcounit : (f : C.₁ x y) → idn ∙ linv f ＝ f
--     lcounit = is-equiv.retr epre

--     runit : (f : C.₁ x y) → rinv (f ∙ idn) ＝ f
--     runit = is-equiv.sec epost

--     rcounit : (f : C.₁ x y) → rinv f ∙ idn ＝ f
--     rcounit = is-equiv.retr epost

--     linv-injective : injective linv
--     linv-injective = is-equiv→injective inv-pre

--     rinv-injective : injective rinv
--     rinv-injective = is-equiv→injective inv-post

--   module _ {x y} (f : C.₁ x y) where
--     fb0 : fiber (idn ∙_) (idn ∙ f)
--     fb0 = lctr (idn ∙ f)

--     fb1 : fiber (_∙ idn) (f ∙ idn)
--     fb1 = rctr (f ∙ idn)

--     u : C.₁ x y
--     u = lctr f .fst

--     v : C.₁ x y
--     v = rctr f .fst

--     p : idn ∙ u ＝ f
--     p = lctr f .snd

--     q : v ∙ idn ＝ f
--     q = rctr f .snd

--     test : u ＝ linv f
--     test = refl

--     test2 : v ＝ rinv f
--     test2 = refl

--   module _ {x y} {f : C.₁ x y} where
--     α : injective (idn ∙_)
--     α = is-equiv→injective (epre {x} {y})

--     β :  injective (_∙ idn)
--     β = is-equiv→injective (epost {x} {y})

--     lpaths : u (idn ∙ f) , p (idn ∙ f) ＝ f , erefl (idn ∙ f)
--     lpaths = is-equiv.fibers epre (f , refl)

--     rpaths : v (f ∙ idn) , q (f ∙ idn) ＝ f , erefl (f ∙ idn)
--     rpaths = is-equiv.fibers epost (f , refl)

--     l0 : u (idn ∙ f) ＝ f
--     l0 = ap fst lpaths

--     l1 : v (f ∙ idn) ＝ f
--     l1 = ap fst rpaths

--   module _ {x y} {f : C.₁ x y} where
--     inj0 : u {x} {y} ∘ (idn ∙_) ＝ id {A = C.₁ x y}
--     inj0 = funext $ λ _ → l0

--     lu0 : u (idn ∙ f) ＝ f
--     lu0 = lunit f

--     adj : (f : C.₁ x y) → ap (idn ∙_) (lunit f) ＝ lcounit (idn ∙ f)
--     adj = eqv-adj epre

--     pre-adj : (i : I) → idn ∙ u (idn ∙ f) ＝ idn ∙ f
--     pre-adj i j = eqv-adj epre f i j

--     post-adj : (i : I) → v (f ∙ idn) ∙ idn ＝ f ∙ idn
--     post-adj i j = eqv-adj epost f i j

--     lu1 : v (f ∙ idn) ＝ f
--     lu1 = runit f

--     inj1 : v {x} {y} ∘ (_∙ idn) ＝ id
--     inj1 = funext $ λ _ → l1

--     σ : u (idn ∙ f) ＝ v (f ∙ idn)
--     σ = l0 ∙ sym l1

--     u0 : C.₁ x x
--     u0 = u idn

--     v0 : C.₁ x x
--     v0 = v idn

--     uq0 : u0 ＝ idn
--     uq0 = subst (λ h → u h ＝ idn) idem (lunit idn)

--     vq0 : v0 ＝ idn
--     vq0 = subst (λ h → v h ＝ idn) idem (runit idn)

--     sll : u (idn ∙ f) ＝ idn ∙ u f
--     sll = lunit f ∙ sym (lcounit f)

--     slr : u (idn ∙ f) ＝ v f ∙ idn
--     slr = lunit f ∙ sym (rcounit f)

--     srl : v (f ∙ idn) ＝ idn ∙ u f
--     srl = runit f ∙ sym (lcounit f)

--     srr : v (f ∙ idn) ＝ v f ∙ idn
--     srr = runit f ∙ sym (rcounit f)

--     vf : u (idn ∙ f ∙ idn) ＝ f ∙ idn
--     vf = lunit (f ∙ idn)

--   --module _ {f : C.₁ x y} where




--       -- lm-filler : (f : C.₁ x y)
--       --           → Square (λ i → contr-map pre (idn ∙ f) .ctr .snd i)
--       --                    (λ i → idn ∙ lmap i)
--       --                    refl
--       --                    refl
--       -- lm-filler f i j = ?

--       -- q1 : idn ∙ h0 ＝ f ∙ idn
--       -- q1 = fb0 (f ∙ idn) .snd

--       -- lpaths : h0 , q1 ＝ f , {!!}
--       -- lpaths = is-equiv.fibers pre {{!!}} ({!!} , {!!})

--       -- h1 : h1 ∙ idn ＝ f ∙ idn
--       -- h1






--       -- w0 : h0 ＝ f
--       -- w0 = {!c1 f!}

--       -- -- q0 : rinv (f ∙ idn) ＝ linv (idn ∙ f)
--       -- -- q0 = runit f ∙ {!!}

--       -- α : linv (idn ∙ f) ＝ rinv (f ∙ idn)
--       -- α = lunit f ∙ sym (runit f)

--       -- eq : idn ∙ f ＝ f ∙ idn
--       -- eq = {!!}




