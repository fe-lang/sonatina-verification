import Prelude.Identity

/-!
# Containers, extensions, and morphisms

Containers, their polynomial extensions, and shape/position morphisms.

A container `C` has a type of shapes `C.Shape` and a type of positions `C.Pos s` at each shape.
Its extension at a type `α` is `C.Ext α = (s : C.Shape) × (C.Pos s → α)`: a shape with an `α` at
each position. The shapes, the positions, and the values have independent universe levels. A
morphism `Hom C D` has a map of the shapes and a backward map of the positions, and
`Hom.apply` is its action on an extension.

```lean
abbrev binary : Container where
  Shape := Unit
  Pos _ := Fin 2

def operands : binary.Ext Nat := ⟨(), fun _ => 3⟩

example : (binary.map (fun n => n + 1) operands).2 ⟨0, by decide⟩ ≡ 4 := .refl
```

A signature that is an `abbrev` shows its types of shapes and of positions to Lean's instance
search.

## Constructions

Each construction has a conversion between its extension and the extensions of its parts.

* `Container.const α` has a shape in `α` and no position.
* `Container.identity` has one shape and one position.
* `C.sum D` has the extension `Sum (C.Ext α) (D.Ext α)`, by `sumIn`, `sumOut`, and `sumIso`.
* `C.product D` has the extension `C.Ext α × D.Ext α`, by `productIn` and `productOut`.
* `C.comp D` has the extension `C.Ext (D.Ext α)`, by `flatten`, `unflatten`, and `compIso`.
* `Container.sigma F` is the sum of a family, with `Hom.inj` and `Hom.copair`.

`Hom.comp` is the action of two morphisms on a composite, and `Hom.unitLeft`, `Hom.unitRight`,
and `Hom.assoc` are the unit and associativity morphisms of composition.
-/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' s''' p''' u v w z

namespace Prelude

/-- A type of shapes with a type of positions at each shape. The shapes and the positions have
independent universe levels. -/
structure Container where
  /-- The shapes. -/
  Shape : Type s
  /-- The positions of a shape. -/
  Pos : Shape → Type p

namespace Container

/-- A shape with an `α` at each of its positions. A position can hold a value or a reference,
and two positions can hold the same reference. -/
def Ext (C : Container.{s, p}) (α : Type u) : Type (max s p u) :=
  (shape : C.Shape) × (C.Pos shape → α)

variable (C : Container.{s, p})
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Relabel positions while retaining the shape. The two types of values can be in different
universes. -/
def map (f : α → β) (x : C.Ext α) : C.Ext β :=
  ⟨x.1, fun i => f (x.2 i)⟩

/-- The map by the identity function is the identity, as an identity in `Type`. -/
def mapId (x : C.Ext α) : C.map id x ≡ x := .refl

/-- The map by a composite is the composite of the maps, as an identity in `Type`. -/
def mapComp (f : α → β) (g : β → γ) (x : C.Ext α) :
    C.map g (C.map f x) ≡ C.map (g ∘ f) x := .refl

/-- Lean's `Functor` interface of an extension, with `map`. -/
instance : Functor C.Ext where
  map := C.map

/-- Lean's `LawfulFunctor` interface of an extension. -/
instance : LawfulFunctor C.Ext where
  map_const := rfl
  id_map _ := rfl
  comp_map _ _ _ := rfl

namespace Ext

/-- Type-valued evidence at every occupied position. -/
def All (P : α → Type v) (x : C.Ext α) : Type (max p v) :=
  (i : C.Pos x.1) → P (x.2 i)

end Ext

/-- A shape map and a contravariant map of positions. The position map can select, repeat, or
reorder the positions of the source. -/
structure Hom (C : Container.{s, p}) (D : Container.{s', p'}) where
  /-- The map of the shapes. -/
  shape : C.Shape → D.Shape
  /-- The backward map of the positions at each shape. -/
  position : (s : C.Shape) → D.Pos (shape s) → C.Pos s

namespace Hom

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}

/-- The identity morphism. -/
def id (C : Container.{s, p}) : Hom C C where
  shape := _root_.id
  position _ := _root_.id

/-- Composition in traversal order: first `f`, then `g`. -/
def trans (f : Hom C D) (g : Hom D E) : Hom C E where
  shape s := g.shape (f.shape s)
  position s i := f.position s (g.position (f.shape s) i)

/-- The action of a morphism on an extension: the image of the shape, with the value at the
source position of each position. -/
def apply (f : Hom C D) (x : C.Ext α) : D.Ext α :=
  ⟨f.shape x.1, fun i => x.2 (f.position x.1 i)⟩

/-- The action of a morphism commutes with a map of the values. -/
def natural (f : Hom C D) (g : α → β) (x : C.Ext α) :
    f.apply (C.map g x) ≡ D.map g (f.apply x) := .refl

/-- The identity morphism is a left unit of composition. -/
def idTrans (f : Hom C D) : (id C).trans f ≡ f := .refl

/-- The identity morphism is a right unit of composition. -/
def transId (f : Hom C D) : f.trans (id D) ≡ f := .refl

/-- Composition of morphisms is associative. -/
def transAssoc {F : Container} (f : Hom C D) (g : Hom D E) (h : Hom E F) :
    (f.trans g).trans h ≡ f.trans (g.trans h) := .refl

/-- The action of the identity morphism is the identity. -/
def applyId (x : C.Ext α) : (id C).apply x ≡ x := .refl

/-- The action of a composite is the composite of the actions. -/
def applyTrans (f : Hom C D) (g : Hom D E) (x : C.Ext α) :
    (f.trans g).apply x ≡ g.apply (f.apply x) := .refl

end Hom

/-- The constant polynomial with value `α`: a shape is a value, and it has no position. -/
def const (α : Type u) : Container.{u, 0} where
  Shape := α
  Pos _ := Empty

/-- The polynomial with no shape. An implementation by calls to it makes no call. -/
def zero : Container.{s, p} where
  Shape := PEmpty
  Pos _ := PEmpty

/-- The polynomial with one shape and one position. -/
def identity : Container.{0, 0} where
  Shape := Unit
  Pos _ := Unit

/-- A choice of a shape from either container. The positions have a `ULift`, so the positions
of the two containers can be in different universes. -/
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

/-- An extension of one of two containers, as an extension of their sum. It adds the lift of
the positions. -/
def sumIn : Sum (C.Ext α) (D.Ext α) → (C.sum D).Ext α
  | .inl x => ⟨.inl x.1, fun i => x.2 i.down⟩
  | .inr x => ⟨.inr x.1, fun i => x.2 i.down⟩

/-- An extension of a sum, as an extension of one of the two containers. It removes the lift
of the positions. -/
def sumOut : (C.sum D).Ext α → Sum (C.Ext α) (D.Ext α)
  | ⟨.inl s, f⟩ => .inl ⟨s, fun i => f ⟨i⟩⟩
  | ⟨.inr s, f⟩ => .inr ⟨s, fun i => f ⟨i⟩⟩

/-- The extension of a sum is the sum of the extensions. The fields `invTo` and `toInv` are
the round-trip identities of `sumIn` and `sumOut`. -/
def sumIso : Iso (Sum (C.Ext α) (D.Ext α)) ((C.sum D).Ext α) where
  to := sumIn
  inv := sumOut
  invTo
    | .inl _ => .refl
    | .inr _ => .refl
  toInv
    | ⟨.inl _, _⟩ => .refl
    | ⟨.inr _, _⟩ => .refl

/-- A pair of extensions of two containers, as an extension of their product. -/
def productIn (x : C.Ext α × D.Ext α) : (C.product D).Ext α :=
  ⟨(x.1.1, x.2.1), fun i => match i with
    | .inl i => x.1.2 i
    | .inr i => x.2.2 i⟩

/-- An extension of a product, as a pair of extensions of the two containers. -/
def productOut (x : (C.product D).Ext α) : C.Ext α × D.Ext α :=
  (⟨x.1.1, fun i => x.2 (.inl i)⟩, ⟨x.1.2, fun i => x.2 (.inr i)⟩)

/-- The first round trip of the product is an identity. The second round trip is the agreement
`productInOut`. -/
def productOutIn (x : C.Ext α × D.Ext α) : productOut (productIn x) ≡ x := .refl

/-- Flatten two layers into the composite container. -/
def flatten (x : C.Ext (D.Ext α)) : (C.comp D).Ext α :=
  ⟨⟨x.1, fun i => (x.2 i).1⟩, fun i => (x.2 i.1).2 i.2⟩

/-- Recover the two layers of a composite extension. -/
def unflatten (x : (C.comp D).Ext α) : C.Ext (D.Ext α) :=
  ⟨x.1.1, fun i => ⟨x.1.2 i, fun j => x.2 ⟨i, j⟩⟩⟩

/-- The extension of a composite is the extension of the outer container at the extension of
the inner container. The fields `invTo` and `toInv` are the round-trip identities of `flatten`
and `unflatten`. -/
def compIso : Iso (C.Ext (D.Ext α)) ((C.comp D).Ext α) :=
  ⟨flatten, unflatten, fun _ => .refl, fun _ => .refl⟩

/-- A map of the values of a composite is the map through the two layers. -/
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

/-- The sum of a family of containers: a choice of an index and of a shape from the container
at that index. The index type has its own universe level. -/
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

/-- The copairing after the inclusion of one member is the morphism at that index. This
identity and `copairInj` are the two equations of the coproduct, and each holds by
computation. -/
def injCopair (f : (i : ι) → Hom (F i) D) (i : ι) : (inj F i).trans (copair f) ≡ f i := .refl

/-- A morphism out of a family sum is the copairing of its restrictions. -/
def copairInj (f : Hom (sigma F) D) : copair (fun i => (inj F i).trans f) ≡ f := .refl

end Hom

end Container

end Prelude
