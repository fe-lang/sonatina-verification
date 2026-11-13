import Prelude.Container.Core

/-! Identity of container extensions from shape and position identities. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v w

namespace Prelude.Container

variable {α : Type u}

namespace Ext

variable (C : Container.{s, p})

/-- Agreement of the shape and every value, retaining the position transport. -/
structure Agreement (x y : C.Ext α) where
  shape : x.1 ≡ y.1
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
  match same with
  | .refl => refl x

def symm {x y : C.Ext α} (same : Agreement C x y) : Agreement C y x :=
  ind (fun x y _ => Agreement C y x) (fun _ _ _ h => ⟨.refl, fun i => (h i).symm⟩) same

def trans {x y z : C.Ext α} (first : Agreement C x y) (second : Agreement C y z) :
    Agreement C x z :=
  ind (fun x y _ => (z : C.Ext α) → Agreement C y z → Agreement C x z)
    (fun _ _ _ h _ second => ⟨second.shape, fun i => (h i).trans (second.values i)⟩)
    first z second

def map {β : Type v} {x y : C.Ext α} (same : Agreement C x y) (f : α → β) :
    Agreement C (C.map f x) (C.map f y) :=
  ⟨same.shape, fun i => Identity.cong f (same.values i)⟩

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

end Ext

variable {C : Container.{s, p}} {D : Container.{s', p'}}

namespace Hom

/-- A morphism at one source shape is an extension of the target container. -/
def component (f : Hom C D) (a : C.Shape) : D.Ext (C.Pos a) :=
  ⟨f.shape a, f.position a⟩

/-- Agreement compares each routing decision using the existing extension relation. -/
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

def transCongr {E : Container.{s'', p''}} {f f' : Hom C D} {g g' : Hom D E}
    (h : Agreement f f') (k : Agreement g g') : Agreement (f.trans g) (f'.trans g') :=
  fun a => k.apply (h a)

end Hom

/-- The second round trip of the product holds at each position. -/
def productInOut (x : (C.product D).Ext α) : Ext.Agreement _ (productIn (productOut x)) x :=
  ⟨.refl, fun i => match i with
    | .inl _ => .refl
    | .inr _ => .refl⟩

end Prelude.Container
