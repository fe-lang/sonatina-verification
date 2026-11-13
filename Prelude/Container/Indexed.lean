import Prelude.Container.Core

/-! Indexed containers with typed positions and type-preserving morphisms. -/

set_option autoImplicit false
set_option genInjectivity false

universe i j o s p s' p' s'' p'' u v w

namespace Prelude

/-- Shapes indexed by outputs, with an input index at each position. -/
structure IndexedContainer (I : Type i) (O : Type o) where
  Shape : O → Type s
  Pos : {o : O} → Shape o → Type p
  index : {o : O} → (s : Shape o) → Pos s → I

namespace IndexedContainer

variable {I : Type i} {J : Type j} {O : Type o}

/-- A shape whose positions carry values of their specified input types. -/
def Ext (C : IndexedContainer.{i, o, s, p} I O) (X : I → Type u) (o : O) :
    Type (max s p u) :=
  (s : C.Shape o) × ((p : C.Pos s) → X (C.index s p))

variable (C : IndexedContainer.{i, o, s, p} I O)
variable {X : I → Type u} {Y : I → Type v} {Z : I → Type w} {o : O}

def map (f : (i : I) → X i → Y i) (x : C.Ext X o) : C.Ext Y o :=
  ⟨x.1, fun p => f (C.index x.1 p) (x.2 p)⟩

def mapId (x : C.Ext X o) : C.map (fun _ => id) x ≡ x := .refl

def mapComp (f : (i : I) → X i → Y i) (g : (i : I) → Y i → Z i)
    (x : C.Ext X o) :
    C.map g (C.map f x) ≡ C.map (fun i => g i ∘ f i) x := .refl

/-- Forget the input indices at a fixed output. -/
def toContainer (o : O) : Container.{s, p} where
  Shape := C.Shape o
  Pos := C.Pos

namespace Ext

/-- A shape identity transports the type index of each position. -/
def indexAlong {a b : C.Shape o} (shape : a ≡ b) (p : C.Pos a) :
    C.index a p ≡ C.index b (Identity.transport (fun s : C.Shape o => C.Pos s) shape p) :=
  match shape with
  | .refl => .refl

structure Agreement (x y : C.Ext X o) where
  shape : x.1 ≡ y.1
  values : (p : C.Pos x.1) →
    Identity.transport X (indexAlong C shape p) (x.2 p) ≡
      y.2 (Identity.transport (fun s : C.Shape o => C.Pos s) shape p)

/-- Type-valued evidence at each typed position. -/
def All (P : (i : I) → X i → Type v) (x : C.Ext X o) : Type (max p v) :=
  (p : C.Pos x.1) → P (C.index x.1 p) (x.2 p)

variable {C}

def Agreement.refl (x : C.Ext X o) : Agreement C x x := ⟨.refl, fun _ => .refl⟩

def Agreement.ofIdentity {x y : C.Ext X o} (same : x ≡ y) : Agreement C x y :=
  match same with
  | .refl => .refl x

def Agreement.symm {x y : C.Ext X o} (same : Agreement C x y) : Agreement C y x := by
  rcases x with ⟨s, values⟩
  rcases y with ⟨t, other⟩
  rcases same with ⟨shape, positions⟩
  cases shape
  exact ⟨.refl, fun p => (positions p).symm⟩

def Agreement.trans {x y z : C.Ext X o} (first : Agreement C x y) (second : Agreement C y z) :
    Agreement C x z := by
  rcases x with ⟨s, values⟩
  rcases y with ⟨t, middle⟩
  rcases z with ⟨u, other⟩
  rcases first with ⟨shape, positions⟩
  rcases second with ⟨shape', positions'⟩
  cases shape
  cases shape'
  exact ⟨.refl, fun p => (positions p).trans (positions' p)⟩

def Agreement.map {x y : C.Ext X o} (same : Agreement C x y) (f : (i : I) → X i → Y i) :
    Agreement C (C.map f x) (C.map f y) :=
  ⟨same.shape, fun p => (Identity.transportMap f (indexAlong C same.shape p) (x.2 p)).trans
    (Identity.cong (f _) (same.values p))⟩

/-- Positionwise evidence follows the shape and value witnesses. -/
def Agreement.all {x y : C.Ext X o} (same : Agreement C x y)
    (P : (i : I) → X i → Type v) (proof : All C P x) : All C P y := by
  rcases x with ⟨s, values⟩
  rcases y with ⟨t, other⟩
  rcases same with ⟨shape, positions⟩
  cases shape
  exact fun p => Identity.transport (P (C.index s p)) (positions p) (proof p)

end Ext

/-- A shape/position morphism with a witness that each input index is preserved. -/
structure Hom (C : IndexedContainer.{i, o, s, p} I O)
    (D : IndexedContainer.{i, o, s', p'} I O) where
  shape : (o : O) → C.Shape o → D.Shape o
  position : {o : O} → (s : C.Shape o) → D.Pos (shape o s) → C.Pos s
  index : {o : O} → (s : C.Shape o) → (p : D.Pos (shape o s)) →
    C.index s (position s p) ≡ D.index (shape o s) p

namespace Hom

variable {C : IndexedContainer.{i, o, s, p} I O}
variable {D : IndexedContainer.{i, o, s', p'} I O}
variable {E : IndexedContainer.{i, o, s'', p''} I O}

def id (C : IndexedContainer.{i, o, s, p} I O) : Hom C C where
  shape _ := _root_.id
  position _ := _root_.id
  index _ _ := .refl

/-- Composition in traversal order: first `f`, then `g`. -/
def trans (f : Hom C D) (g : Hom D E) : Hom C E where
  shape o s := g.shape o (f.shape o s)
  position s p := f.position s (g.position (f.shape _ s) p)
  index s p := (f.index s (g.position (f.shape _ s) p)).trans (g.index (f.shape _ s) p)

/-- Interpret a morphism, transporting values along its input-index witnesses. -/
def apply (f : Hom C D) (x : C.Ext X o) : D.Ext X o :=
  ⟨f.shape o x.1, fun p =>
    Identity.transport X (f.index x.1 p) (x.2 (f.position x.1 p))⟩

/-- Agreement includes the computational witnesses for preservation of type indices. -/
structure Agreement (f g : Hom C D) where
  shape : (o : O) → (s : C.Shape o) → f.shape o s ≡ g.shape o s
  position : {o : O} → (s : C.Shape o) → (p : D.Pos (f.shape o s)) →
    f.position s p ≡ g.position s
      (Identity.transport (fun t : D.Shape o => D.Pos t) (shape o s) p)
  index : {o : O} → (s : C.Shape o) → (p : D.Pos (f.shape o s)) →
    (f.index s p).trans (Ext.indexAlong D (shape o s) p) ≡
      (Identity.cong (C.index s) (position s p)).trans
        (g.index s (Identity.transport (fun t : D.Shape o => D.Pos t) (shape o s) p))

private def valueAlong (x : C.Ext X o) {p q : C.Pos x.1} (same : p ≡ q) :
    Identity.transport X (Identity.cong (C.index x.1) same) (x.2 p) ≡ x.2 q :=
  match same with
  | .refl => .refl

/-- Agreement of index witnesses induces agreement of the transported values. -/
def Agreement.apply {f g : Hom C D} (same : Agreement f g) (x : C.Ext X o) :
    Ext.Agreement D (f.apply x) (g.apply x) := by
  refine ⟨same.shape o x.1, ?_⟩
  intro p
  let q := Identity.transport (fun t : D.Shape o => D.Pos t) (same.shape o x.1) p
  exact (Identity.transportTrans X (f.index x.1 p)
    (Ext.indexAlong D (same.shape o x.1) p) (x.2 (f.position x.1 p))).symm.trans
    ((Identity.cong (fun path => Identity.transport X path (x.2 (f.position x.1 p)))
      (same.index x.1 p)).trans
    ((Identity.transportTrans X (Identity.cong (C.index x.1) (same.position x.1 p))
      (g.index x.1 q) (x.2 (f.position x.1 p))).trans
    (Identity.cong (Identity.transport X (g.index x.1 q)) (valueAlong x (same.position x.1 p)))))

def natural (f : Hom C D) (g : (i : I) → X i → Y i) (x : C.Ext X o) :
    Ext.Agreement D (f.apply (C.map g x)) (D.map g (f.apply x)) :=
  ⟨.refl, fun p => Identity.transportMap g (f.index x.1 p) (x.2 (f.position x.1 p))⟩

def idTrans (f : Hom C D) : Agreement ((id C).trans f) f where
  shape _ _ := .refl
  position _ _ := .refl
  index s p := Identity.transRefl (f.index s p)

def transId (f : Hom C D) : Agreement (f.trans (id D)) f where
  shape _ _ := .refl
  position _ _ := .refl
  index s p := (Identity.transRefl ((f.index s p).trans .refl)).trans (Identity.transRefl (f.index s p))

def transAssoc {F : IndexedContainer I O} (f : Hom C D) (g : Hom D E)
    (h : Hom E F) : Agreement ((f.trans g).trans h) (f.trans (g.trans h)) where
  shape _ _ := .refl
  position _ _ := .refl
  index s p := (Identity.transRefl _).trans (Identity.transAssoc
    (f.index s (g.position (f.shape _ s) (h.position (g.shape _ (f.shape _ s)) p)))
    (g.index (f.shape _ s) (h.position (g.shape _ (f.shape _ s)) p))
    (h.index (g.shape _ (f.shape _ s)) p))

def applyId (x : C.Ext X o) : (id C).apply x ≡ x := .refl

def applyTrans (f : Hom C D) (g : Hom D E) (x : C.Ext X o) :
    Ext.Agreement E ((f.trans g).apply x) (g.apply (f.apply x)) :=
  ⟨.refl, fun p => Identity.transportTrans X
    (f.index x.1 (g.position (f.shape _ x.1) p))
    (g.index (f.shape _ x.1) p)
    (x.2 (f.position x.1 (g.position (f.shape _ x.1) p)))⟩

end Hom

/-- The identity polynomial on indexed families. -/
def identity (I : Type i) : IndexedContainer.{i, i, 0, 0} I I where
  Shape _ := Unit
  Pos _ := Unit
  index {o} _ _ := o

/-- A constant indexed family. -/
def const (X : O → Type u) : IndexedContainer.{i, o, u, 0} I O where
  Shape := X
  Pos _ := Empty
  index _ p := p.elim

/-- Substitute a container at each input index of the outer container. -/
def comp (C : IndexedContainer.{j, o, s, p} J O)
    (D : IndexedContainer.{i, j, s', p'} I J) :
    IndexedContainer.{i, o, max s p s', max p p'} I O where
  Shape o := (s : C.Shape o) × ((p : C.Pos s) → D.Shape (C.index s p))
  Pos s := (p : C.Pos s.1) × D.Pos (s.2 p)
  index s p := D.index (s.2 p.1) p.2

variable {C : IndexedContainer.{j, o, s, p} J O}
variable {D : IndexedContainer.{i, j, s', p'} I J}

def flatten (x : C.Ext (D.Ext X) o) : (C.comp D).Ext X o :=
  ⟨⟨x.1, fun p => (x.2 p).1⟩, fun p => (x.2 p.1).2 p.2⟩

def unflatten (x : (C.comp D).Ext X o) : C.Ext (D.Ext X) o :=
  ⟨x.1.1, fun p => ⟨x.1.2 p, fun q => x.2 ⟨p, q⟩⟩⟩

def unflattenFlatten (x : C.Ext (D.Ext X) o) : unflatten (flatten x) ≡ x := .refl

def flattenUnflatten (x : (C.comp D).Ext X o) : flatten (unflatten x) ≡ x := .refl

def flattenMap (f : (i : I) → X i → Y i) (x : C.Ext (D.Ext X) o) :
    flatten (C.map (fun _ => D.map f) x) ≡ (C.comp D).map f (flatten x) := .refl

end IndexedContainer

/-- Regard an ordinary container as a polynomial on a single index. -/
def Container.indexed (C : Container.{s, p}) : IndexedContainer.{0, 0, s, p} Unit Unit where
  Shape _ := C.Shape
  Pos := C.Pos
  index _ _ := ()

end Prelude
