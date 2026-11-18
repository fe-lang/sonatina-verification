import Prelude.Container.Core

/-!
# Agreement of extensions and of morphisms

Identity of container extensions from shape and position identities.

Agreement of two elements of an extension has an identity of the shapes and an identity of the
values at each position. A shape of a composite has a function, so agreement at a composite
needs an identity of two functions. The agreement of the two layers has an identity of the
outer shapes, an identity of the inner shapes at each position, and an identity of the values:
it needs no identity of two functions. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' s''' p''' u v w

namespace Prelude.Container

variable {α : Type u}

namespace Ext

variable (C : Container.{s, p})

/-- Agreement of the shape and every value, retaining the position transport. Agreement is
reflexive, symmetric, and transitive (`refl`, `symm`, `trans`), and a map of the values keeps it
(`map`). -/
structure Agreement (x y : C.Ext α) where
  /-- The identity of the two shapes. -/
  shape : x.1 ≡ y.1
  /-- The identity of the two values at each position, across the transport of the position. -/
  values : (i : C.Pos x.1) → x.2 i ≡ y.2 (Identity.transport C.Pos shape i)

namespace Agreement

variable {C}

/-- Eliminate the shape identity while retaining the supplied position witnesses. -/
def ind (motive : (x y : C.Ext α) → Agreement C x y → Sort w)
    (base : (a : C.Shape) → (f g : C.Pos a → α) → (h : Homotopy f g) →
      motive ⟨a, f⟩ ⟨a, g⟩ ⟨.refl, h⟩)
    {x y : C.Ext α} (h : Agreement C x y) : motive x y h :=
  Identity.ind (fun b shape => (g : C.Pos b → α) →
    (values : (i : C.Pos x.1) → x.2 i ≡ g (Identity.transport C.Pos shape i)) →
      motive x ⟨b, g⟩ ⟨shape, values⟩)
    (fun g values => base x.1 x.2 g values) h.shape y.2 h.values

def refl (x : C.Ext α) : Agreement C x x := ⟨.refl, fun _ => .refl⟩

def ofIdentity {x y : C.Ext α} (same : x ≡ y) : Agreement C x y :=
  Identity.ind (fun y _ => Agreement C x y) (refl x) same

def symm {x y : C.Ext α} (same : Agreement C x y) : Agreement C y x :=
  ind (fun x y _ => Agreement C y x) (fun _ _ _ h => ⟨.refl, fun i => (h i).symm⟩) same

def trans {x y z : C.Ext α} (first : Agreement C x y) (second : Agreement C y z) :
    Agreement C x z :=
  ind (fun x y _ => (z : C.Ext α) → Agreement C y z → Agreement C x z)
    (fun _ _ _ h _ second => ⟨second.shape, fun i => (h i).trans (second.values i)⟩)
    first z second

/-- A function of the values keeps the agreement. -/
def map {β : Type v} {x y : C.Ext α} (same : Agreement C x y) (f : α → β) :
    Agreement C (C.map f x) (C.map f y) :=
  ⟨same.shape, fun i => Identity.cong f (same.values i)⟩

/-- Two functions that are identical at each value give maps that agree, at two elements that
agree. -/
def mapCongr {β : Type v} {x y : C.Ext α} {f g : α → β}
    (same : Agreement C x y) (h : Homotopy f g) :
    Agreement C (C.map f x) (C.map g y) :=
  ⟨same.shape, fun i => (Identity.cong f (same.values i)).trans
    (h (y.2 (Identity.transport C.Pos same.shape i)))⟩

/-- A value-indexed specification is carried across each position separately. -/
def all {x y : C.Ext α} (same : Agreement C x y) (P : α → Type v)
    (proof : All C P x) : All C P y :=
  ind (fun x y _ => All C P x → All C P y)
    (fun _ _ _ h proof i => Identity.transport P (h i) (proof i)) same proof

end Agreement

/-- Agreement of two elements of the extension of a composite, at the two layers: the outer
shapes are identical, the inner shapes are identical at each position of the outer shape, and
the values are identical. It needs no identity of two functions. The relation is reflexive and
transitive (`refl`, `trans`). -/
structure CompAgreement {D : Container.{s, p}} {E : Container.{s', p'}}
    (x y : (D.comp E).Ext α) where
  outer : x.1.1 ≡ y.1.1
  inner : (i : D.Pos x.1.1) → x.1.2 i ≡ y.1.2 (Identity.transport D.Pos outer i)
  values : (i : D.Pos x.1.1) → (j : E.Pos (x.1.2 i)) →
    x.2 ⟨i, j⟩ ≡ y.2 ⟨Identity.transport D.Pos outer i, Identity.transport E.Pos (inner i) j⟩

namespace CompAgreement

variable {D : Container.{s, p}} {E : Container.{s', p'}}

/-- The elimination of the identity of the outer shapes. The identities of the inner shapes
stay, one for each position. -/
def ind {motive : (x y : (D.comp E).Ext α) → CompAgreement x y → Sort w}
    (base : (d : D.Shape) → (φ φ' : D.Pos d → E.Shape) →
      (vals : ((i : D.Pos d) × E.Pos (φ i)) → α) → (vals' : ((i : D.Pos d) × E.Pos (φ' i)) → α) →
      (inner : (i : D.Pos d) → φ i ≡ φ' i) →
      (values : (i : D.Pos d) → (j : E.Pos (φ i)) →
        vals ⟨i, j⟩ ≡ vals' ⟨i, Identity.transport E.Pos (inner i) j⟩) →
      motive ⟨⟨d, φ⟩, vals⟩ ⟨⟨d, φ'⟩, vals'⟩ ⟨.refl, inner, values⟩)
    {x y : (D.comp E).Ext α} (h : CompAgreement x y) : motive x y h :=
  Identity.ind
    (fun d' outer => (φ' : D.Pos d' → E.Shape) →
      (vals' : ((i : D.Pos d') × E.Pos (φ' i)) → α) →
      (inner : (i : D.Pos x.1.1) → x.1.2 i ≡ φ' (Identity.transport D.Pos outer i)) →
      (values : (i : D.Pos x.1.1) → (j : E.Pos (x.1.2 i)) →
        x.2 ⟨i, j⟩ ≡
          vals' ⟨Identity.transport D.Pos outer i, Identity.transport E.Pos (inner i) j⟩) →
      motive x ⟨⟨d', φ'⟩, vals'⟩ ⟨outer, inner, values⟩)
    (fun φ' vals' inner values => base x.1.1 x.1.2 φ' x.2 vals' inner values)
    h.outer y.1.2 y.2 h.inner h.values

def refl (x : (D.comp E).Ext α) : CompAgreement x x := ⟨.refl, fun _ => .refl, fun _ _ => .refl⟩

def trans {x y z : (D.comp E).Ext α} (h : CompAgreement x y) (k : CompAgreement y z) :
    CompAgreement x z :=
  ind (motive := fun x y _ => (z : (D.comp E).Ext α) → CompAgreement y z → CompAgreement x z)
    (fun _ _ _ _ _ inner values z k =>
      ⟨k.outer, fun i => (inner i).trans (k.inner i), fun i j =>
        (values i j).trans
          ((k.values i (Identity.transport E.Pos (inner i) j)).trans
            (Identity.cong (fun w => z.2 ⟨Identity.transport D.Pos k.outer i, w⟩)
              (Identity.transportTrans E.Pos (inner i) (k.inner i) j).symm))⟩)
    h z k

/-- A function of the values keeps the agreement. -/
def map {β : Type v} (f : α → β) {x y : (D.comp E).Ext α} (h : CompAgreement x y) :
    CompAgreement ((D.comp E).map f x) ((D.comp E).map f y) :=
  ⟨h.outer, h.inner, fun i j => Identity.cong f (h.values i j)⟩

end CompAgreement

end Ext

variable {C : Container.{s, p}} {D : Container.{s', p'}}

namespace Hom

/-- A morphism at one source shape is an extension of the target container. -/
def component (f : Hom C D) (a : C.Shape) : D.Ext (C.Pos a) :=
  ⟨f.shape a, f.position a⟩

/-- Agreement compares each routing decision using the existing extension relation: the shape
and the backward position map of the two morphisms agree at each source shape, in
`Ext.Agreement`. -/
def Agreement (f g : Hom C D) :=
  (a : C.Shape) → Ext.Agreement D (f.component a) (g.component a)

namespace Agreement

def refl (f : Hom C D) : Agreement f f := fun a => Ext.Agreement.refl (f.component a)

def symm {f g : Hom C D} (h : Agreement f g) : Agreement g f :=
  fun a => (h a).symm

def trans {f g k : Hom C D} (h : Agreement f g) (j : Agreement g k) : Agreement f k :=
  fun a => (h a).trans (j a)

def ofIdentity {f g : Hom C D} (h : f ≡ g) : Agreement f g :=
  Identity.ind (fun g _ => Agreement f g) (refl f) h

/-- Value action respects agreement in both the morphism and the supplied extension. -/
def apply {f g : Hom C D} {x y : C.Ext α} (h : Agreement f g)
    (k : Ext.Agreement C x y) : Ext.Agreement D (f.apply x) (g.apply y) :=
  Ext.Agreement.ind (fun x y _ => Ext.Agreement D (f.apply x) (g.apply y))
    (fun a _ _ values => Ext.Agreement.mapCongr (h a) values) k

end Agreement

/-- Composition respects agreement of the two morphisms. -/
def transCongr {E : Container.{s'', p''}} {f f' : Hom C D} {g g' : Hom D E}
    (h : Agreement f f') (k : Agreement g g') : Agreement (f.trans g) (f'.trans g') :=
  fun a => k.apply (h a)

/-- The position map of a morphism commutes with a transport along an identity of shapes. -/
def positionTransport (f : Hom C D) {a b : C.Shape} (e : a ≡ b) (i : D.Pos (f.shape a)) :
    Identity.transport C.Pos e (f.position a i) ≡
      f.position b (Identity.transport D.Pos (Identity.cong f.shape e) i) :=
  Identity.ind
    (fun b e => Identity.transport C.Pos e (f.position a i) ≡
      f.position b (Identity.transport D.Pos (Identity.cong f.shape e) i))
    .refl e

/-- Two morphisms into a composite agree at the two layers, at each shape. -/
def CompAgreement {E : Container.{s'', p''}} (f g : Hom C (D.comp E)) :=
  (a : C.Shape) → Ext.CompAgreement (f.component a) (g.component a)

end Hom

/-- The action of two morphisms on a composite keeps the agreement of the two layers. -/
def Ext.CompAgreement.comp {E : Container.{s, p}} {C' : Container.{s'', p''}}
    {D' : Container.{s''', p'''}} (f : Hom E C') (g : Hom D D') {x y : (E.comp D).Ext α}
    (h : Ext.CompAgreement x y) :
    Ext.CompAgreement ((Hom.comp f g).apply x) ((Hom.comp f g).apply y) :=
  Ext.CompAgreement.ind
    (motive := fun x y _ =>
      Ext.CompAgreement ((Hom.comp f g).apply x) ((Hom.comp f g).apply y))
    (fun d φ _ _ vals' inner values =>
      ⟨.refl, fun i => Identity.cong g.shape (inner (f.position d i)), fun i j =>
        (values (f.position d i) (g.position (φ (f.position d i)) j)).trans
          (Identity.cong (fun w => vals' ⟨f.position d i, w⟩)
            (g.positionTransport (inner (f.position d i)) j))⟩)
    h

/-- The second round trip of the product holds at each position: it is an agreement, with an
identity at each left position and at each right position. -/
def productInOut (x : (C.product D).Ext α) : Ext.Agreement _ (productIn (productOut x)) x :=
  ⟨.refl, fun i => match i with
    | .inl _ => .refl
    | .inr _ => .refl⟩

end Prelude.Container
