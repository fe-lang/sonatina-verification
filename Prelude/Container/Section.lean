import Prelude.Container.Agreement

/-! Closed providers, specifications, and dependent evidence for container interfaces.
`DepPoly` is Aberlé's `def:deppoly`, and `Evidence` is the one-call case of `⇒Dep`:
verification retains the supplied precondition witness and depends on the actual
response. Reindexing consumes identities of responses, not of whole functions.
-/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v w z w' z' w'' z''

namespace Prelude.Container

def Section (C : Container.{s, p}) := (a : C.Shape) → C.Pos a

namespace Ext

variable {C : Container.{s, p}} {α : Type u}

def run (x : C.Ext α) (provider : Section C) : α := x.2 (provider x.1)

def Agreement.run {x y : C.Ext α} {f g : Section C}
    (h : Agreement C x y) (k : Homotopy f g) : x.run f ≡ y.run g :=
  ind (fun x y _ => x.run f ≡ y.run g)
    (fun a left _ values => (Identity.cong left (k a)).trans (values (g a))) h

end Ext

namespace Hom

variable {C : Container.{s, p}} {D : Container.{s', p'}}

def run (f : Hom C D) (provider : Section D) : Section C :=
  fun a => (f.component a).run provider

def runCongr {f g : Hom C D} {provider provider' : Section D}
    (h : Agreement f g) (k : Homotopy provider provider') :
    Homotopy (f.run provider) (g.run provider') := fun a => (h a).run k

def runTrans {E : Container.{s'', p''}} (f : Hom C D) (g : Hom D E)
    (provider : Section E) :
    Homotopy ((f.trans g).run provider) (f.run (g.run provider)) := fun _ => .refl

def runId (provider : Section C) : Homotopy ((Hom.id C).run provider) provider :=
  fun _ => .refl

end Hom

variable {C : Container.{s, p}}

/-- A specification of an interface: a precondition on each shape, and a postcondition on each
response that depends on the witness of the precondition. -/
structure DepPoly (C : Container.{s, p}) where
  Pre : C.Shape → Type w
  Post : (a : C.Shape) → Pre a → C.Pos a → Type z

namespace DepPoly

variable {P : DepPoly.{s, p, w, z} C} {Q : DepPoly.{s, p, w', z'} C}
  {T : DepPoly.{s, p, w'', z''} C}

/-- A map over one interface takes an admission forward and evidence for each response
back to the postcondition of the supplied admission. -/
abbrev Map (P : DepPoly.{s, p, w, z} C) (Q : DepPoly.{s, p, w', z'} C) :=
  (a : C.Shape) → (pre : P.Pre a) →
    (q : Q.Pre a) × ((o : C.Pos a) → Q.Post a q o → P.Post a pre o)

def Map.id (P : DepPoly.{s, p, w, z} C) : Map P P :=
  fun _ pre => ⟨pre, fun _ post => post⟩

def Map.trans (f : Map P Q) (g : Map Q T) : Map P T :=
  fun a pre =>
    let ⟨q, back⟩ := f a pre
    let ⟨t, back'⟩ := g a q
    ⟨t, fun o post => back o (back' o post)⟩

/-- A cartesian map identifies the two fibres of response evidence at the mapped admission. -/
abbrev Cartesian (P : DepPoly.{s, p, w, z} C) (Q : DepPoly.{s, p, w', z'} C) :=
  (a : C.Shape) → (pre : P.Pre a) →
    (q : Q.Pre a) × ((o : C.Pos a) → Iso (Q.Post a q o) (P.Post a pre o))

def Cartesian.toMap (f : Cartesian P Q) : Map P Q :=
  fun a pre => ⟨(f a pre).1, fun o => ((f a pre).2 o).to⟩

def Cartesian.id (P : DepPoly.{s, p, w, z} C) : Cartesian P P :=
  fun _ pre => ⟨pre, fun _ => Iso.refl _⟩

def Cartesian.comp (f : Cartesian P Q) (g : Cartesian Q T) : Cartesian P T :=
  fun a pre => ⟨(g a (f a pre).1).1, fun o => ((g a (f a pre).1).2 o).trans ((f a pre).2 o)⟩

end DepPoly

/-- The specification of a family sum that has a given specification at each index. This is
Aberlé's `sumDep`. -/
def DepPoly.sigma {ι : Type u} {F : ι → Container.{s, p}}
    (r : (i : ι) → DepPoly.{s, p, w, z} (F i)) : DepPoly.{max u s, p, w, z} (sigma F) where
  Pre a := (r a.1).Pre a.2
  Post a := (r a.1).Post a.2

/-- Evidence that a closed provider satisfies a specification. -/
def Evidence (r : DepPoly.{s, p, w, z} C) (provider : Section C) :=
  (a : C.Shape) → (pre : r.Pre a) → r.Post a pre (provider a)

/-- The graph of a closed provider: the specification that has the response of the provider at
each shape. -/
def Section.graph (f : Section C) : DepPoly.{s, p, 0, p} C where
  Pre _ := PUnit
  Post a _ b := f a ≡ b

/-- A closed provider has evidence of its graph. -/
def Section.graphEvidence (f : Section C) : Evidence f.graph f := fun _ _ => .refl

/-- The closed provider of the polynomial with no shape. -/
def Section.zero : Section Container.zero.{s, p} := fun a => nomatch a

/-- The specification of the polynomial with no shape. -/
def DepPoly.zero : DepPoly.{s, p, w, z} Container.zero where
  Pre _ := PEmpty
  Post _ _ _ := PEmpty

/-- The specification that admits no call: no shape has a witness of its precondition. -/
def DepPoly.noCall (C : Container.{s, p}) : DepPoly.{s, p, w, z} C where
  Pre _ := PEmpty
  Post _ pre _ := nomatch pre

/-- Each specification of the polynomial with no shape has evidence. -/
def Evidence.zero (r : DepPoly.{s, p, w, z} Container.zero) : Evidence r Section.zero :=
  fun a => nomatch a

namespace Evidence

variable {r : DepPoly.{s, p, w, z} C} {f g h : Section C}

def reindex (same : Homotopy f g) (e : Evidence r f) : Evidence r g :=
  fun a pre => Identity.transport (r.Post a pre) (same a) (e a pre)

def reindexRefl (e : Evidence r f) (a : C.Shape) (pre : r.Pre a) :
    reindex (Homotopy.refl f) e a pre ≡ e a pre := .refl

def reindexTrans (same : Homotopy f g) (next : Homotopy g h)
    (e : Evidence r f) (a : C.Shape) (pre : r.Pre a) :
    reindex (same.trans next) e a pre ≡ reindex next (reindex same e) a pre :=
  Identity.transportTrans (r.Post a pre) (same a) (next a) (e a pre)

def reindexSymm (same : Homotopy f g) (e : Evidence r f)
    (a : C.Shape) (pre : r.Pre a) :
    reindex same.symm (reindex same e) a pre ≡ e a pre :=
  Identity.transportSymm (r.Post a pre) (same a) (e a pre)

def reindexCongr (same : Homotopy f g) {e e' : Evidence r f}
    (k : (a : C.Shape) → (pre : r.Pre a) → e a pre ≡ e' a pre)
    (a : C.Shape) (pre : r.Pre a) : reindex same e a pre ≡ reindex same e' a pre :=
  Identity.cong (Identity.transport (r.Post a pre) (same a)) (k a pre)

end Evidence
end Prelude.Container
