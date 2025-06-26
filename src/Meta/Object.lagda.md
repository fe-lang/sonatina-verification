```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Object where

open import Prim.Type hiding (Quiver; quiver)
open import Data.Sigma.Type
open import Data.Pi hiding (_∙_)
--open import Meta.Cut

record Object : Typeω where
  no-eta-equality
  constructor obj
  field
    {l₀} : Level → Level
    ₀ : ∀ {u} → Type (l₀ u)

record Quiver (O : Object) : Typeω where
  no-eta-equality
  constructor mor
  open Object O public
  field
    {l₁} : Level → Level → Level
    ₁ : ∀ {u v} → ₀ {u} → ₀ {v} → Type (l₁ u v)

  level : Level → Level → Level
  level u v = l₀ u ⊔ l₀ v ⊔ l₁ u v

module _ {O : Object} (C : Quiver O)  where
  private
    module C = Quiver C
    level = λ (u v w : Level) → C.level u v ⊔ C.level v w ⊔ C.level u w


  record LComposable u v w : Type (level u v w) where
    field seq : {x : C.₀ {u}} {y : C.₀ {v}} {z : C.₀ {w}}
              → C.₁ x y → C.₁ y z → C.₁ x z

module _ {o h} {Ob : Type o} (Hom : Ob → Ob → Type h) where
--   morphism : Quiver (obj Ob)
--   morphism = mor Hom

--   Composable : Type (o ⊔ h)
--   Composable = LComposable morphism o o o

--   module _ {x y} (f : Hom x y) where
--     Precomp = ∀ {z} → Hom y z → Hom x z
--     Postcomp = ∀ {w} → Hom w x → Hom w y


-- ```

--   is-eqv : {x y : Ob} (g : Hom x y) → Type j
--   is-eqv {x} {y} g =   ((z : Ob) → is-equiv λ (h : Hom y z) → h ⋄ g)
--                      × ((w : Ob) → is-equiv λ (f : Hom w x) → g ⋄ f)

--   ∀ {z} (k : Hom y z) → is-contr (fiber (λ (h : Hom y z) → h ⋄ g) k)
--         - ctr : fiber (_∘ g) k
--               m : Hom y z , p : g * m ＝ k
--         - paths : (h : fiber (_∘ g) k) → ctr ＝ h
--               - so we get that
--   ∀ {w} (k : Hom w x) → is-contr (fiber (λ (h : Hom w x) → g ∘ f) k)

-- ```
--   record has-factor {x y z}
--      (fam : Hom x y → Hom y z → Hom x z → Type h)
--      (k : Hom x z) (g : Hom y z) : Type (o ⊔ h ₊) where
--     field
--       map : Hom x y
--       center : fam map g k
--       path-ind : (P : (f : Hom x y) → fam f g k → Type h)
--                → (f' : Hom x y) (q : fam f' g k)
--                → P map center → P f' q

--     unit : Hom y z → Hom y z
--     unit = path-ind (λ _ _ → Hom y z) map center

--   module _ (fam : ∀ {x y z} → Hom x y → Hom y z → Hom x z → Type h) where
--     record has-factor {x y z} (f : Hom x y) (k : Hom x z) : Type (o ⊔ h ₊) where
--       field
--         map : Hom y z
--         witness  fam f map k
--         slice : has-factor fam k map

--       private
--         c : Hom x y
--         c = has-factor.map slice

--         tr : (P : (f : Hom x y) → Type h) → P c → P f
--         tr P = has-factor.path-ind slice (λ h q → P h) f witness

--   record is-factorizable {x z} (k : Hom x z) y : Type (o ⊔ h ₊) where
--     field
--       map : Hom x y
--       fam : Hom x y → Hom x z → Type h
--       center : fam map k
--       path-ind : (P : (f : Hom x y) → fam f k → Type h)
--                → (f : Hom x y) (q : fam f k)
--                → P map center → P f q

--   record has-composition  : Type (o ⊔ h ₊) where
--     field
--       comp-str : ∀ {x y z} (f : Hom x y)  (g : Hom y z)
--                → Σ h ∶ Hom x z , is-factorizable h y

--     infixr 40 _∙_
--     _∙_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
--     _∙_ f g = comp-str f g .fst

--     fam : ∀ {x y z} → Hom x y → Hom y z → Hom x z → Type h
--     fam f g = is-factorizable.fam (comp-str f g .snd) f

--     field
--       coh : ∀ {x y z} (f : Hom x y) (g : Hom y z) → fam f g (f ∙ g)

--     module _ {x y z} (f : Hom x y) (g : Hom y z) where
--       private module str = is-factorizable (comp-str f g .snd)

--       factor : Hom x y
--       factor = str.map

--       module sys where
--         private module factor = is-factorizable (comp-str factor g .snd)
--         center : factor.fam factor.map (comp-str str.map g .fst)
--         center = factor.center

--         ind : (P : (f : Hom x y) → factor.fam f (factor ∙ g) → Type h)
--             → (f : Hom x y) (q : factor.fam f (factor ∙ g))
--             → P factor.map factor.center → P f q
--         ind = factor.path-ind

--       ct : str.fam str.map (f ∙ g)
--       ct = str.center

--       tr : (P : Hom x y → Type h) (f : Hom x y) → str.fam {!!} ({!!} ∙ g) → P (str.map) → P f
--       tr P k q p = sys.ind (λ h _ → P h) k {!q!} {!!}

--       center : str.fam f (f ∙ g)
--       center = coh f g

--       c : str.fam f (factor ∙ g)
--       c = sys.ind (λ h p → str.fam h (factor ∙ g)) f {!!} {!!} where
--         sys = is-factorizable.center {!!}

--       slice-ind : (P : (f : Hom x y) → fam f g (f ∙ g) → Type h)
--                 → P factor {!!} → {!!}
--       slice-ind = {!!}

--     comp-ind : ∀ {x y z} {g : Hom y z}
--               → (P : (f : Hom x y) (k : Hom x z) → fam f g k → Type h)
--               → {f : Hom x y} (k : Hom x z) (q : fam f g k)
--               → P (factor f g) (factor f g ∙ g) {!!} → P f k q
--     comp-ind {g} P {f} k q = {!!}

--     --path-ind :



--     -- private module ps {z} {g : Hom x z} = is-composition (post-equiv g)
--     --         module pr {w} {g : Hom w y} = is-composition (pre-equiv g)



--   record Idn {x} (i : Hom x x) : Type (o ⊔ h ₊) where
--     field
--       -- "fam" is the witness that a hom `f : w -> x` and `f : x ->  y`
--       -- composes to produce a hom `w -> y`; it is our analogy to the def
--       -- of fiber, where `fam f g h` ought to represent the second
--       -- component of `fiber (_∙ g) h`.
--       -- We must then add the structure which portrays the contractibility
--       -- of the hom under h.
--       fam : ∀ {w y} → Hom w x → Hom x y → Hom w y → Type h
--       slice-ind : ∀ {w y} {g : Hom x y} {k : Hom w y}
--                 → (P : (f : Hom w x) → fam f g k → Type h)
--                 → {f f' : Hom w x}
--                 → (q : fam f g k) (q' : fam f' g k)
--                 → P f q → P f' q'
--       lunit : ∀ {y} (f : Hom x y) → Σ i ∶ Hom x x , fam i f f

--     idn-ind : ∀ {y} {f : Hom x y} (P : (i : Hom x x) → fam i f f → Type h)
--               → (q : fam i f f)
--               → (let (c , ρ) = lunit f)
--               → P c ρ → P i q
--     idn-ind P q = slice-ind (λ h s → P h s) (lunit _ .snd) q

--       -- we now induce a unique `f`, this represents the action of post-composing
--       -- the identity map, which determines a unique `f` in the slice category
--       -- ctr : ∀ {w y} (f : Hom x y) → Σ f ∶ Hom w x , fam f i f
--       -- -- Every predicate dependent on the witness of the post-composition of
--       -- -- the identity map with some f is propositional
--       -- path : ∀ {w} (P : (k : Hom w x) → fam i k → Type h)
--       --      →  (f : Hom w x) (s r : fam i f)
--       --      → P f s → P f r
--       -- -- Next, we specify the action of pre-composing the identity map,
--       -- -- which yields the witness that nothing was altered in composing
--       -- -- some f. Note that we fix some `i : Hom x x` which may be distinct
--       -- op-ctr : ∀ {y} (f : Hom x y) → fam f f
--       -- -- Path induction here is more subtle; what we require is that we
--       -- -- show that the `i` given in op-ctr is ultimately contractible
--       -- op-path : ∀ {y} (P : (k : Hom x y) → fam k k → Type h)
--       --         → (f : Hom x y) (q : fam f f) → P f (op-ctr f) → P f q


--     --lunit :
--       -- l-ind : ∀ {y} (P : (f : Hom x y) → fam f → Type h)
--       --       → (f : Hom x y) (q : fam f) → P f (lctr f) → P f q
--       -- r-ind : ∀ {w} (P : (f : Hom w x) → fam f → Type h)
--       --       → (f : Hom w x) (q : fam f) → P f (rctr f) → P f q
--       -- c-ind : (P : ∀ {w y} (g : Hom x y) (h : Hom w y) → fam h → Type h)
--       --       → ∀ {w y} (g : Hom x y) (h : Hom w y) (h : ) (q : fam h)
--       --       → P g {!!} → P h q → Σ f ∶ Hom w x , P {!!} {!!}

--     -- ictr : fam i
--     -- ictr = c-ind (λ x _ _ → fam x) (lctr i) (rctr i)

--     --field
--       --Disp[_∙_] : ∀ {w y} (f : Hom w x) (g : Hom x y) → fam f → fam g → Type h
--       -- lunit : ∀ {y} (f : Hom x y) → Disp[ i ∙ f ] ictr (lctr f)
--       -- runit : ∀ {w} (f : Hom w x) → Disp[ f ∙ i ] (rctr f) ictr
--       --idem : Disp[ i ∙ i ] ictr ictr
--       -- ind : ∀ {y} (g : Hom x y) (q : fam g)
--       --     → (P : ∀ {w} → (f : Hom w x) (r : fam f)
--       --                → Disp[ f ∙ g ] r q → Type h)
--       --     → ∀ {w y} {f f' : Hom w x} {}
--       --     → (p : Disp[ f ∙ g ] {!!} {!!}) (q : Disp[ f' ∙ g ] {!!} {!!})
--       --     → P {!!} {!!} {!!}

--       -- ind : ∀ {w} {f : Hom w x}
--       --     → (P : ∀ {y} (g : Hom x y) (k : Hom w y) → fam f g k → Type h)
--       --     → ∀ {y} (g : Hom x y)
--       --     → Σ h ∶ Hom w y , Σ q ∶ fam f g h
--       --     , ((h' : Hom w y) (r : fam f g h') → P g h q → P g h' r)

--     -- lunit : ∀ {y} (f : Hom x y) → fam i f f
--     -- lunit f = ind (λ {z} g k q → fam {!!} {!!} {!!}) {!!} .snd .snd {!!} {!!} {!!}

--     -- runit : ∀ {w} (f : Hom w x) → fam f i f
--     -- runit f = {!!}

--     --   ctr-ind : ∀ {y} {g : Hom x y}
--     --           → (P : ∀ {w} {f : Hom w x} (l : Hom w y) → fam f g l → Type h)
--     --           → ∀ {w} (f f' : Hom w x) {k : Hom w y}
--     --           → (q : fam f g k) (r : fam f' g k) → P k q → P k r


--     -- open import Data.Path.Type hiding (_∙_)

--     _∙_ : ∀ {w y} → Hom w x → Hom x y → Hom w y
--     _∙_ {w} {y} f g = {!!}


--     -- -- Composition is unique!
--     -- comp-unique : ∀ {w y} (f : Hom w x) (g : Hom x y)
--     --             → (h₁ h₂ : Hom w y) → (q₁ : fam f g h₁) → (q₂ : fam f g h₂)
--     --             → h₁ ＝ h₂
--     -- comp-unique {w} {y} f g h₁ h₂ q₁ q₂ = ind (λ {a} {b} {φ} {ψ} k f → _ ＝ k) {!!} {!!} {!refl!} f g .snd .snd .fst {!!} {!!} {!!}


--     -- lunit : ∀ {y} (f : Hom x y) → {!!} ∙ {!!} ＝ {!!}
--     -- lunit f = {!!}


-- -- The type of large categories
-- record Cat : Typeω where
--   field
--     {O} : Object
--     Quiver-cat : Quiver O
--     Composable-cat : ∀ {u v w} → LComposable Quiver-cat u v w

--   open Quiver Quiver-cat public
--   field
--     rx : ∀ {u} {x : ₀ {u}} → ₁ x x

-- -- module Quiver {o h} (Ob : Type o) (Hom : Ob → Ob → Type h) where
-- --   quiver : LQuiver
-- --   quiver = mor Ob Hom

-- -- --graph : ∀ {u}

-- -- record Display (C : Cat) : Typeω where
-- --   private module C = Cat C
-- --   field
-- --     {l₀} : Level → Level
-- --     {l₁} : Level → Level → Level
-- --     Ob[_] : ∀ {u} → C.₀ {u} → Type (l₀ u)
-- --     Hom[_] : ∀ {u v} {x : C.₀ {u}} {y : C.₀ {v}}
-- --            → C.₁ x y → Ob[ x ] → Ob[ y ] → Type (l₁ u v)
-- --     drx : ∀ {u} {x : C.₀ {u}} {a : Ob[ x ]} → Hom[ C.rx ] a a




-- -- -- module Arr : Type (u ⊔ v) where
-- -- --   ∀

-- -- -- record ωGraph : Typeω where
-- -- --   no-eta-equality
-- -- --   constructor graph
-- -- --   field
-- -- --     {l₀} : Level
-- -- --     {l₁} : Level
-- -- --     ₀ : Type l₀
-- -- --     ₁ : ₀ → ₀ → Type l₁

-- -- -- Composable : (C : ωGraph)
-- -- --            → (let module C = ωGraph C)
-- -- --            → Type (C.l₀ ⊔ C.l₁)
-- -- -- Composable C = ∀ {x y z} → C.₁ x y → C.₁ y z → C.₁ x z
-- -- --   where module C = ωGraph C
-- -- -- --         → Type ( Quiver.l₀ C u
-- -- -- --                   ⊔ Quiver.l₀ C v
-- -- -- --                   ⊔ Quiver.l₀ C w
-- -- -- --                   ⊔ Quiver.l₁ C u v
-- -- -- --                   ⊔ Quiver.l₁ C v w
-- -- -- --                   ⊔ Quiver.l₁ C u w
-- -- -- --                   )
-- -- -- -- Composable {u} {v} {w} C =
-- -- -- --   where module C = Quiver C
-- -- -- -- instance
-- -- -- --   Cut-Composable : Hom-Cut C.₁
-- -- -- --   Cut-Composable .Cut.seq = {!seq!}

-- -- -- record Category o h : Type₊ (o ⊔ h) where
-- -- --   field
-- -- --     Ob : Type o
-- -- --     Hom : Ob → Ob → Type h
-- -- --     comp : Composable (graph Ob Hom)


-- -- -- private module test {ℓ ℓ'} (Ob : Type ℓ) (Arr : Ob → Ob → Type ℓ') where
-- -- --   Mor : Quiver
-- -- --   Mor = mor (λ {_} → Ob) Arr

-- -- -- record Display (C : Quiver) : Typeω where
-- -- --   private module C = Quiver C
-- -- --   field
-- -- --     {ℓ-obd} : Level → Level
-- -- --     {ℓ-homd} : Level → Level → Level → Level
-- -- --     Ob[_] : ∀ {u} → C.₀ {u} → Type (ℓ-obd (C.l₀ u))
-- -- --     Hom[_] : ∀ {u v} {A : C.₀ {u}} {B : C.₀ {v}}
-- -- --            → C.₁ A B → Ob[ A ] → Ob[ B ]
-- -- --            → Type (ℓ-homd
-- -- --                      (C.l₁ u v)
-- -- --                      (ℓ-obd (C.l₀ u))
-- -- --                      (ℓ-obd (C.l₀ v)))

-- -- -- -- record Object : Typeω where
-- -- -- --   constructor hom
-- -- -- --   field
-- -- -- --     {ℓ₀} : Level
-- -- -- --     {adj} : Level → Level
-- -- -- --     {₀} : Type ℓ₀
-- -- -- --     ₁ : ₀ → ₀ → Type (adj ℓ₀)

-- -- -- --   ℓ₁ = adj ℓ₀
-- -- -- --   ℓ = ℓ₀ ⊔ ℓ₁
