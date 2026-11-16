import Prelude.Identity

/-! Containers, their polynomial extensions, and shape/position morphisms. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' s''' p''' u v w z

namespace Prelude

/-- A type of shapes with a type of positions at each shape. -/
structure Container where
  Shape : Type s
  Pos : Shape → Type p

namespace Container

/-- A shape with an `α` at each of its positions. -/
def Ext (C : Container.{s, p}) (α : Type u) : Type (max s p u) :=
  (shape : C.Shape) × (C.Pos shape → α)

variable (C : Container.{s, p})
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Relabel positions while retaining the shape. -/
def map (f : α → β) (x : C.Ext α) : C.Ext β :=
  ⟨x.1, fun i => f (x.2 i)⟩

def mapId (x : C.Ext α) : C.map id x ≡ x := .refl

def mapComp (f : α → β) (g : β → γ) (x : C.Ext α) :
    C.map g (C.map f x) ≡ C.map (g ∘ f) x := .refl

instance : Functor C.Ext where
  map := C.map

instance : LawfulFunctor C.Ext where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

namespace Ext

/-- Type-valued evidence at every occupied position. -/
def All (P : α → Type v) (x : C.Ext α) : Type (max p v) :=
  (i : C.Pos x.1) → P (x.2 i)

end Ext

/-- A shape map and a contravariant map of positions. -/
structure Hom (C : Container.{s, p}) (D : Container.{s', p'}) where
  shape : C.Shape → D.Shape
  position : (s : C.Shape) → D.Pos (shape s) → C.Pos s

namespace Hom

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}

def id (C : Container.{s, p}) : Hom C C where
  shape := _root_.id
  position _ := _root_.id

/-- Composition in traversal order: first `f`, then `g`. -/
def trans (f : Hom C D) (g : Hom D E) : Hom C E where
  shape s := g.shape (f.shape s)
  position s i := f.position s (g.position (f.shape s) i)

def apply (f : Hom C D) (x : C.Ext α) : D.Ext α :=
  ⟨f.shape x.1, fun i => x.2 (f.position x.1 i)⟩

def natural (f : Hom C D) (g : α → β) (x : C.Ext α) :
    f.apply (C.map g x) ≡ D.map g (f.apply x) := .refl

def idTrans (f : Hom C D) : (id C).trans f ≡ f := .refl

def transId (f : Hom C D) : f.trans (id D) ≡ f := .refl

def transAssoc {F : Container} (f : Hom C D) (g : Hom D E) (h : Hom E F) :
    (f.trans g).trans h ≡ f.trans (g.trans h) := .refl

def applyId (x : C.Ext α) : (id C).apply x ≡ x := .refl

def applyTrans (f : Hom C D) (g : Hom D E) (x : C.Ext α) :
    (f.trans g).apply x ≡ g.apply (f.apply x) := .refl

end Hom

/-- The constant polynomial with value `α`. -/
def const (α : Type u) : Container.{u, 0} where
  Shape := α
  Pos _ := Empty

/-- The polynomial with no shape. -/
def zero : Container.{s, p} where
  Shape := PEmpty
  Pos _ := PEmpty

/-- The polynomial with one shape and one position. -/
def identity : Container.{0, 0} where
  Shape := Unit
  Pos _ := Unit

/-- A choice of a shape from either container. -/
def sum (C : Container.{s, p}) (D : Container.{s', p'}) :
    Container.{max s s', max p p'} where
  Shape := Sum C.Shape D.Shape
  Pos
    | .inl a => ULift.{p'} (C.Pos a)
    | .inr b => ULift.{p} (D.Pos b)

/-- A pair of shapes with the positions of both components. -/
def product (C : Container.{s, p}) (D : Container.{s', p'}) :
    Container.{max s s', max p p'} where
  Shape := C.Shape × D.Shape
  Pos s := Sum (C.Pos s.1) (D.Pos s.2)

/-- Polynomial substitution: `(C.comp D).Ext α` represents `C.Ext (D.Ext α)`. -/
def comp (C : Container.{s, p}) (D : Container.{s', p'}) :
    Container.{max s p s', max p p'} where
  Shape := (s : C.Shape) × (C.Pos s → D.Shape)
  Pos s := (i : C.Pos s.1) × D.Pos (s.2 i)

variable {C : Container.{s, p}} {D : Container.{s', p'}}

def sumIn : Sum (C.Ext α) (D.Ext α) → (C.sum D).Ext α
  | .inl x => ⟨.inl x.1, fun i => x.2 i.down⟩
  | .inr x => ⟨.inr x.1, fun i => x.2 i.down⟩

def sumOut : (C.sum D).Ext α → Sum (C.Ext α) (D.Ext α)
  | ⟨.inl s, f⟩ => .inl ⟨s, fun i => f ⟨i⟩⟩
  | ⟨.inr s, f⟩ => .inr ⟨s, fun i => f ⟨i⟩⟩

/-- The extension of a sum is the sum of the extensions. -/
def sumIso : Iso (Sum (C.Ext α) (D.Ext α)) ((C.sum D).Ext α) where
  to := sumIn
  inv := sumOut
  invTo
    | .inl _ => .refl
    | .inr _ => .refl
  toInv
    | ⟨.inl _, _⟩ => .refl
    | ⟨.inr _, _⟩ => .refl

def productIn (x : C.Ext α × D.Ext α) : (C.product D).Ext α :=
  ⟨(x.1.1, x.2.1), fun i => match i with
    | .inl i => x.1.2 i
    | .inr i => x.2.2 i⟩

def productOut (x : (C.product D).Ext α) : C.Ext α × D.Ext α :=
  (⟨x.1.1, fun i => x.2 (.inl i)⟩, ⟨x.1.2, fun i => x.2 (.inr i)⟩)

def productOutIn (x : C.Ext α × D.Ext α) : productOut (productIn x) ≡ x := .refl

/-- Flatten two layers into the composite container. -/
def flatten (x : C.Ext (D.Ext α)) : (C.comp D).Ext α :=
  ⟨⟨x.1, fun i => (x.2 i).1⟩, fun i => (x.2 i.1).2 i.2⟩

/-- Recover the two layers of a composite extension. -/
def unflatten (x : (C.comp D).Ext α) : C.Ext (D.Ext α) :=
  ⟨x.1.1, fun i => ⟨x.1.2 i, fun j => x.2 ⟨i, j⟩⟩⟩

/-- The extension of a composite is the extension of the outer container at the extension of
the inner container. -/
def compIso : Iso (C.Ext (D.Ext α)) ((C.comp D).Ext α) :=
  ⟨flatten, unflatten, fun _ => .refl, fun _ => .refl⟩

def flattenMap (f : α → β) (x : C.Ext (D.Ext α)) :
    flatten (C.map (D.map f) x) ≡ (C.comp D).map f (flatten x) := .refl

namespace Hom

variable {C' : Container.{s'', p''}} {D' : Container.{s''', p'''}}

/-- The action of two morphisms on a composite. -/
def comp (f : Hom C C') (g : Hom D D') : Hom (C.comp D) (C'.comp D') where
  shape a := ⟨f.shape a.1, fun i => g.shape (a.2 (f.position a.1 i))⟩
  position a i := ⟨f.position a.1 i.1, g.position (a.2 (f.position a.1 i.1)) i.2⟩

/-- The left unit of the composition product. -/
def unitLeft (C : Container.{s, p}) : Hom C (identity.comp C) :=
  ⟨fun a => ⟨(), fun _ => a⟩, fun _ i => i.2⟩

/-- The right unit of the composition product. -/
def unitRight (C : Container.{s, p}) : Hom C (C.comp identity) :=
  ⟨fun a => ⟨a, fun _ => ()⟩, fun _ i => i.1⟩

/-- The associativity of the composition product. -/
def assoc (C : Container.{s, p}) (D : Container.{s', p'}) (E : Container.{s'', p''}) :
    Hom ((C.comp D).comp E) (C.comp (D.comp E)) where
  shape a := ⟨a.1.1, fun i => ⟨a.1.2 i, fun j => a.2 ⟨i, j⟩⟩⟩
  position _ i := ⟨⟨i.1, i.2.1⟩, i.2.2⟩

end Hom

/-- A choice of an index and of a shape from the container at that index. -/
def sigma {ι : Type z} (F : ι → Container.{s, p}) : Container.{max z s, p} where
  Shape := (i : ι) × (F i).Shape
  Pos a := (F a.1).Pos a.2

namespace Hom

variable {ι : Type z} {F : ι → Container.{s, p}}

/-- The inclusion of one member of a family. -/
def inj (F : ι → Container.{s, p}) (i : ι) : Hom (F i) (sigma F) where
  shape a := ⟨i, a⟩
  position _ := _root_.id

/-- The morphism out of a family sum that has a given morphism at each index. -/
def copair (f : (i : ι) → Hom (F i) D) : Hom (sigma F) D where
  shape a := (f a.1).shape a.2
  position a := (f a.1).position a.2

def injCopair (f : (i : ι) → Hom (F i) D) (i : ι) : (inj F i).trans (copair f) ≡ f i := .refl

/-- A morphism out of a family sum is the copairing of its restrictions. -/
def copairInj (f : Hom (sigma F) D) : copair (fun i => (inj F i).trans f) ≡ f := .refl

end Hom

end Container

end Prelude
