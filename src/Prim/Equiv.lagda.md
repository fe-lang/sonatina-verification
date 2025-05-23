```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Equiv where

open import Prim.Type
  using (Level; Type; _⊔_; id; const)
  renaming (funcomp to infixr 40 _∘_)
open import Prim.Pi
open import Prim.Fiber
open import Prim.Interval.Core
open import Prim.Interval.Transport using (coe; transport; transport-refl; module coe; is-contr→extend)
open import Prim.Interval.Kan using (hcomp; _∙∙_∙∙_ ; path-filler)
open import Prim.Interval.Fill
  using (neutral-square; module tri; path-cfiller)

open import Prim.Data.Path
open import Prim.Data.Sigma
open import Prim.Data.Contr
open import Prim.Data.Qinv

infix 4 _≃_

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    contr-map : (y : B) → is-contr (fiber f y)

  fun = f

  center : (y : B) → fiber f y
  center y = contr-map y .ctr

  inv : B → A
  inv y = center y .fst

  fibers : {y : B} (fb : fiber f y) → center y ＝ fb
  fibers {y} = contr-map y .paths

  sec : (x : A) → inv (f x) ＝ x
  sec x i = fibers (x , refl) i .fst

  retr :  (y : B) → f (inv y) ＝ y
  retr y = center y .snd

  abstract
    adj : (x : A) → ap f (sec x) ＝ retr (f x)
    adj x = Square.transpose (tri.by-pre _ _ _ (Square.hsym (fp x))) where
      fp : (x : A) → Square (retr (f x)) (ap f (sec x)) (erefl (f x)) (erefl (f x))
      fp x i j = fibers (x , refl) i .snd j

    inv-adj : ∀ y → ap inv (retr y) ＝ sec (inv y)
    inv-adj y =
      let
        pf : (x : A) → ap inv (retr (f x)) ＝ sec (inv (f x))
        pf x i j = hcomp (∂ i ∨ ∂ j) λ where
          k (i = i0) → inv (retr (f x) (j ∨ ~ k))
          k (i = i1) → sec (sec x (~ k)) j
          k (j = i0) → inv (adj x (~ i) (~ k))
          k (j = i1) → sec x (i ∧ ~ k)
          k (k = i0) → sec x (i ∧ j)
      in
        transp (λ i → ap inv (retr (retr y i)) ＝ sec (inv (retr y i)))
          i0 (pf (inv y))

open is-equiv public
  renaming ( fun to eqv-fun
           ; inv to eqv-inv
           ; sec to eqv-sec
           ; retr to eqv-retr
           ; adj to eqv-adj
           ; inv-adj to eqv-adj⁻¹ )


_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv
{-# BUILTIN EQUIV      _≃_   #-}

Equiv = _≃_

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN   eqvtofun  #-}

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (contr-map (w .snd) a)

{-# BUILTIN EQUIVPROOF equiv-proof #-}

ap-coh : ∀ {u} {A : Type u} {x y : A} (p : x ＝ y)
                → ap (λ x → x) p ＝ p
ap-coh = erefl

eqv-refl : ∀ {u} (A : Type u) → A ≃ A
eqv-refl A .fst = id
eqv-refl A .snd .contr-map y .ctr = y , refl
eqv-refl A .snd .contr-map y .paths fb i .fst = singl-contr (y , fb .snd) (~ i) .fst
eqv-refl A .snd .contr-map y .paths fb i .snd j = fb .snd (~ i ∨ j)

is-hae : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → Type (u ⊔ v)
is-hae {A} {B} f = Σ g ∶ (B → A)
                 , Σ s ∶ (∀ x → g (f x) ＝ x)
                 , Σ r ∶ (∀ y → f (g y) ＝ y)
                 , ∀ x → ap f (s x) ＝ r (f x)

hae→equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
          → is-hae f → is-equiv f
hae→equiv {A} {B} {f} (g , η , ε , α) .contr-map = contr where
  module _ {y : B} ((x , p) : fiber f y) where
    path : g y ＝ x
    path = ap g (sym p) ∙∙ refl ∙∙ η x

    filler : ε y ⌞ ap f path ⌟ p ⇒ refl
    filler i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → ε (p k) j
      k (i = i1) → neutral-square (ap f (η x)) p j k
      k (j = i0) → f (path-filler (ap g p) refl (η x) i k)
      k (j = i1) → p k
      k (k = i0) → α x (~ i) j

  prop : {y : B} (z : fiber f y) → Path (fiber f y) (g y , ε y) z
  prop z i .fst = path z i
  prop z i .snd = filler z i

  contr : (y : B) → is-contr (fiber f y)
  contr y .ctr = g y , ε y
  contr y .paths = prop

module Equiv {u v} {A : Type u} {B : Type v} ((f , e) : A ≃ B) where
  private
    module e = is-equiv e

  to = f
  from = e.inv
  inverse : B ≃ A
  inverse = e.inv , hae→equiv (f , e.retr , e.sec , e.inv-adj)

open Equiv public

equiv→qinv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
           → is-equiv f → has-qinv f
equiv→qinv e .qinv-inv = eqv-inv e
equiv→qinv e .qinv-sec = eqv-sec e
equiv→qinv e .qinv-retr = eqv-retr e

qinv→equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
           → has-qinv f → is-equiv f
qinv→equiv q .contr-map = qinv→contr-map q  

Qinv→Equiv : ∀ {u v} {A : Type u} {B : Type v} (e : Qinv A B) → A ≃ B
Qinv→Equiv e = e .fst , qinv→equiv (e .snd)

equiv : ∀ {u v} {A : Type u} {B : Type v}
      → (f : A → B) (g : B → A)
      → (∀ x → g (f x) ＝ x)
      → (∀ y → f (g y) ＝ y)
      → is-equiv f
equiv f g s r = qinv→equiv q
  where
    q : has-qinv f
    q .qinv-inv = g
    q .qinv-sec = s
    q .qinv-retr = r

-- Constructor for _≃_
≃-intro : ∀ {u v} {A : Type u} {B : Type v}
      → (f : A → B) (g : B → A)
      → (∀ x → g (f x) ＝ x)
      → (∀ y → f (g y) ＝ y)
      → A ≃ B
≃-intro f g s r .fst = f
≃-intro f g s r .snd = qinv→equiv q
  where
    q : has-qinv f
    q .qinv-inv = g
    q .qinv-sec = s
    q .qinv-retr = r

Equiv→Qinv : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → Qinv A B
Equiv→Qinv e = e .fst , equiv→qinv (e .snd)

transport-is-equiv : ∀ {ℓ} (A : I → Type ℓ) → is-equiv (transport (λ i → A i))
transport-is-equiv A = hae→equiv (g , η , ε , α)
  where
    f = transport (λ i → A i)
    g = transport (λ i → A (~ i))
    η = transport.unit A
    ε = transport.counit A
    α = transport.adj A

id-equiv : ∀ {u} {A : Type u} → is-equiv {A = A} (λ x → x)
id-equiv .contr-map x .ctr .fst = x
id-equiv .contr-map x .ctr .snd = refl
id-equiv .contr-map x .paths (y , p) i  = p (~ i) , λ j → p (~ i ∨ j)

pathtoeqv : ∀ {u} {A B : Type u} → A ＝ B → A ≃ B
pathtoeqv P = transport P , transport-is-equiv λ i → P i

module _ {u v w} {A : Type u} {B : Type v} {C : Type w} {h : A → B}
  (e : is-equiv h)
  where
  private module e = is-equiv e
  precomp-is-equiv : is-equiv (λ (k : B → C) → k ∘ h)
  precomp-is-equiv = equiv (λ k → k ∘ h) (_∘ e.inv)
    (λ k → ap (k ∘_) (funext $ e.retr))
    (λ k → ap (k ∘_) (funext $ e.sec))

  postcomp-is-equiv : is-equiv (λ (k : C → A) → h ∘ k)
  postcomp-is-equiv = equiv (λ k → h ∘ k) (e.inv ∘_)
   (λ k → ap (_∘ k) (funext $ e.sec))
   λ k → ap (_∘ k) (funext $ e.retr)


-- has-section : ∀ {u v} {A : Type u} {B : Type v} → (B → A) → Type (u ⊔ v)
-- has-section {A} {B} r = Σ s ∶ (A → B) , ((x : A) → r (s x) ＝ x)

-- has-retract : ∀ {u v} {A : Type u} {B : Type v} → (B → A) → Type (u ⊔ v)
-- has-retract {A} {B} s = Σ r ∶ (A → B) , ((y : B) → r (s y) ＝ y)

-- module _ {u v} {A : Type u} {B : Type v} where
--   has-left-coh : (s : A → B) → has-retract s → Type (u ⊔ v)
--   has-left-coh s (r , r-s) = Σ s-r ∶ ((y : B) → s (r y) ＝ y)
--                          , ((y : B) → ap r (s-r y) ＝ r-s (r y))

--   has-right-coh : (r : A → B) → has-section r → Type (u ⊔ v)
--   has-right-coh r (s , r-s) = Σ s-r ∶ ((x : A) → s (r x) ＝ x)
--                           , ((x : A) → ap r (s-r x) ＝ r-s (r x))

--   is-right-coh : (f : A → B) → Type (u ⊔ v)
--   is-right-coh f = Σ (has-right-coh f)

--   has-right-coh→equiv : {f : A → B} (s : has-section f) → has-right-coh f s → is-equiv f
--   has-right-coh→equiv (g , r) (s , coh) .eqv-inv = g
--   has-right-coh→equiv (g , r) (s , coh) .eqv-sec = s
--   has-right-coh→equiv (g , r) (s , coh) .eqv-retr = r
--   has-right-coh→equiv (g , r) (s , coh) .eqv-adj = coh

--   equiv→has-right-coh : {f : A → B} (e : is-equiv f)
--                   → has-right-coh f (eqv-inv e , eqv-retr e)
--   equiv→has-right-coh e .fst = eqv-sec e
--   equiv→has-right-coh e .snd = eqv-adj e

--   is-right-coh→equiv : (f : A → B) → is-right-coh f → is-equiv f
--   is-right-coh→equiv f (s , coh) = has-right-coh→equiv s coh

--   equiv→is-right-coh : (f : A → B) → is-equiv f → is-right-coh f
--   equiv→is-right-coh f e .fst .fst = eqv-inv e
--   equiv→is-right-coh f e .fst .snd = eqv-retr e
--   equiv→is-right-coh f e .snd = equiv→has-right-coh e

--   module equiv-coh where
--     sec : {f : A → B} (x : is-right-coh f)
--         → equiv→is-right-coh f (is-right-coh→equiv f x) ＝ x
--     sec ((g , s) , r , coh) i .fst .fst = g
--     sec ((g , s) , r , coh) i .fst .snd = s
--     sec ((g , s) , r , coh) i .snd .fst = r
--     sec ((g , s) , r , coh) i .snd .snd = coh

--     retr : {f : A → B} (e : is-equiv f)
--          → is-right-coh→equiv f (equiv→is-right-coh f e) ＝ e
--     retr e i .eqv-inv = eqv-inv e
--     retr e i .eqv-sec = eqv-sec e
--     retr e i .eqv-retr = eqv-retr e
--     retr e i .eqv-adj = eqv-adj e

--     adj : {f : A → B} (e : is-equiv f)
--         → ap (equiv→is-right-coh f) (retr e) ＝ sec (equiv→is-right-coh f e)
--     adj e i j .fst .fst = eqv-inv e
--     adj e i j .fst .snd = eqv-retr e
--     adj e i j .snd .fst = eqv-sec e
--     adj e i j .snd .snd = eqv-adj e

--     retr-equiv : (f : A → B) → is-equiv (equiv→is-right-coh f)
--     retr-equiv f .eqv-inv = is-right-coh→equiv f
--     retr-equiv f .eqv-sec = retr
--     retr-equiv f .eqv-retr = sec
--     retr-equiv f .eqv-adj = adj

-- is-right-coh≃is-equiv : ∀ {u v} {A : Type u} {B : Type v}
--               → (f : A → B) → is-right-coh f ≃ is-equiv f
-- is-right-coh≃is-equiv f =
--   equiv (is-right-coh→equiv f) (equiv→is-right-coh f) equiv-coh.sec equiv-coh.retr

-- contr-map→is-equiv : ∀ {u v} {A : Type u} {B : Type v}
--                    → {f : A → B} → is-contr-map f → is-equiv f
-- contr-map→is-equiv {A} {B} {f} e = γ where
--   module e = is-contr-map e
--   g : B → A
--   g = e.inv

--   s : (x : A) → g (f x) ＝ x
--   s x i = e.fiber-paths (x , refl) i .fst

--   r : (y : B) → f (g y) ＝ y
--   r y = e.center y .snd

--   fp : (x : A) → Square (r (f x)) (ap f (s x)) (erefl (f x)) (erefl (f x))
--   fp x i j = e.fiber-paths (x , refl) i .snd j

--   a : (x : A) → Square (ap f (s x)) refl (r (f x)) refl
--   a x = Square.transpose (tri.by-pre _ _ _ (Square.hsym (fp x)))

--   γ : is-equiv f
--   γ .eqv-inv = g
--   γ .eqv-sec = s
--   γ .eqv-retr = r
--   γ .eqv-adj = a
