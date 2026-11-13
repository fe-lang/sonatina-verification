import Prelude.Container.Section

/-! Computations that call a container interface, and implementations of one interface by
calls to another. This is Aberlé's `Free` and `def:implementation`. A computation has
functions as continuations, so its laws are structural agreements.

The functions on an agreement use `casesOn` with an explicit motive. A generated matcher on
this family eliminates `Prop` equalities of the two computations, and the elaborator then
normalizes the computations again at each step. Transitivity eliminates its first agreement,
and it gives the first computation to a function of its second agreement. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' s''' p''' u v w z

namespace Prelude.Container

/-- A computation that returns an `α` after a well-founded sequence of calls to `C`. Each call
selects a shape and continues with the response at a position of that shape. -/
inductive Free (C : Container.{s, p}) (α : Type u) : Type (max s p u) where
  | pure (value : α) : Free C α
  | request (shape : C.Shape) (next : C.Pos shape → Free C α) : Free C α

namespace Free

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
variable {α : Type u} {β : Type v} {γ : Type w}

/-- One call that returns its response. -/
def call (a : C.Shape) : Free C (C.Pos a) := .request a .pure

/-- Continue each returned value with a computation. -/
def bind : Free C α → (α → Free C β) → Free C β
  | .pure a, f => f a
  | .request a k, f => .request a (fun i => (k i).bind f)

def map (f : α → β) (x : Free C α) : Free C β := x.bind (fun a => .pure (f a))

/-- Interpret each call by a closed provider. -/
def run (provider : Section C) : Free C α → α
  | .pure a => a
  | .request a k => run provider (k (provider a))

/-- Equal returned values, and the same call with agreement of the continuations at each
response. -/
inductive Agreement : Free C α → Free C α → Type (max s p u) where
  | pure {a b : α} (value : a ≡ b) : Agreement (.pure a) (.pure b)
  | request (shape : C.Shape) {k k' : C.Pos shape → Free C α}
      (next : (i : C.Pos shape) → Agreement (k i) (k' i)) :
      Agreement (.request shape k) (.request shape k')

namespace Agreement

def refl : (x : Free C α) → Agreement x x
  | .pure _ => .pure .refl
  | .request a k => .request a (fun i => refl (k i))

def ofIdentity {x y : Free C α} (same : x ≡ y) : Agreement x y :=
  Identity.ind (fun y _ => Agreement x y) (refl x) same

def symm {x y : Free C α} (h : Agreement x y) : Agreement y x :=
  Agreement.casesOn (motive := fun x y _ => Agreement y x) h
    (fun {_ _} e => .pure e.symm)
    (fun a {_ _} next => .request a (fun i => (next i).symm))

/-- An agreement with `z` for each computation that agrees with `y` in one step. That
computation returns a value identical to the value of `y`, or it has the call of `y` and
continuations that have an agreement with `w` for each agreement of a continuation of `y`
with `w`. -/
def Before : Free C α → Free C α → Type (max s p u)
  | .pure b, z => (a : α) → a ≡ b → Agreement (.pure a) z
  | .request shape k', z => (k : C.Pos shape → Free C α) →
      ((i : C.Pos shape) → (w : Free C α) → Agreement (k' i) w → Agreement (k i) w) →
      Agreement (.request shape k) z

def before {y z : Free C α} (h : Agreement y z) : Before y z :=
  Agreement.casesOn (motive := fun y z _ => Before y z) h
    (fun {_ _} e' _ e => .pure (e.trans e'))
    (fun shape {_ k''} next' _ step => .request shape (fun i => step i (k'' i) (next' i)))

def trans {x y z : Free C α} (h : Agreement x y) (second : Agreement y z) : Agreement x z :=
  Agreement.casesOn (motive := fun x y _ => (z : Free C α) → Agreement y z → Agreement x z) h
    (fun {a _} e _ second => second.before a e)
    (fun _ {k _} next _ second => second.before k (fun i _ h => (next i).trans h))
    z second

/-- Bind respects agreement of the computation and of each continuation. -/
def bind {x y : Free C α} {f g : α → Free C β} (h : Agreement x y)
    (k : (a : α) → Agreement (f a) (g a)) : Agreement (x.bind f) (y.bind g) :=
  Agreement.casesOn (motive := fun x y _ => Agreement (x.bind f) (y.bind g)) h
    (fun {a _} e => Identity.ind (fun b _ => Agreement (f a) (g b)) (k a) e)
    (fun a {_ _} next => .request a (fun i => (next i).bind k))

/-- Agreeing computations return the same value from agreeing providers. -/
def run {f g : Section C} {x y : Free C α} (h : Agreement x y) (same : Homotopy f g) :
    x.run f ≡ y.run g :=
  Agreement.casesOn (motive := fun x y _ => x.run f ≡ y.run g) h
    (fun {_ _} e => e)
    (fun a {_ k'} next =>
      ((next (f a)).run same).trans (Identity.cong (fun i => (k' i).run g) (same a)))

end Agreement

def pureBind (a : α) (f : α → Free C β) : (Free.pure a).bind f ≡ f a := .refl

def bindPure : (x : Free C α) → Agreement (x.bind .pure) x
  | .pure _ => .pure .refl
  | .request a k => .request a (fun i => bindPure (k i))

def bindAssoc (f : α → Free C β) (g : β → Free C γ) :
    (x : Free C α) → Agreement ((x.bind f).bind g) (x.bind (fun a => (f a).bind g))
  | .pure a => .refl ((f a).bind g)
  | .request a k => .request a (fun i => bindAssoc f g (k i))

def runBind (provider : Section C) (f : α → Free C β) :
    (x : Free C α) → (x.bind f).run provider ≡ (f (x.run provider)).run provider
  | .pure _ => .refl
  | .request a k => runBind provider f (k (provider a))

end Free

/-- An implementation of `C` by calls to `D`: a computation for each shape of `C` that returns
a response of that shape. -/
def Impl (C : Container.{s, p}) (D : Container.{s', p'}) : Type (max s p s' p') :=
  (a : C.Shape) → Free D (C.Pos a)

/-- An implementation with one call at each shape. -/
def Hom.toImpl {C : Container.{s, p}} {D : Container.{s', p'}} (f : Hom C D) : Impl C D :=
  fun a => .request (f.shape a) (fun i => .pure (f.position a i))

namespace Free

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
variable {α : Type u} {β : Type v}

/-- Replace each call to `C` with its implementation. -/
def subst (g : Impl C D) : Free C α → Free D α
  | .pure a => .pure a
  | .request a k => (g a).bind (fun i => subst g (k i))

end Free

namespace Impl

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
  {G : Container.{s''', p'''}}

def id (C : Container.{s, p}) : Impl C C := Free.call

/-- Composition in traversal order: the calls of `f` are implemented by `g`. -/
def trans (f : Impl C D) (g : Impl D E) : Impl C E := fun a => (f a).subst g

/-- The closed provider of `C` that an implementation gives from a closed provider of `D`. -/
def run (f : Impl C D) (provider : Section D) : Section C := fun a => (f a).run provider

/-- The implementation of a family sum that has a given implementation at each index. -/
def copair {ι : Type z} {F : ι → Container.{s, p}} (f : (i : ι) → Impl (F i) D) :
    Impl (sigma F) D := fun a => f a.1 a.2

/-- The implementation that returns the response of a closed provider without a call. An
operation with such an implementation is pure. -/
def ofSection (f : Section C) : Impl C D := fun a => .pure (f a)

def ofSectionRun (f : Section C) (provider : Section D) :
    Homotopy ((ofSection f).run provider) f := fun _ => .refl

/-- The implementation of a shape returns without a call: it agrees with the computation that
returns one response. -/
structure Returns (f : Impl C D) (a : C.Shape) where
  response : C.Pos a
  agrees : Free.Agreement (f a) (.pure response)

/-- A shape that returns without a call gives its response to the continuation. -/
def Returns.bind {f : Impl C D} {a : C.Shape} (r : f.Returns a) {β : Type z}
    (k : C.Pos a → Free D β) : Free.Agreement ((f a).bind k) (k r.response) :=
  r.agrees.bind (fun i => .refl (k i))

def Agreement (f g : Impl C D) := (a : C.Shape) → Free.Agreement (f a) (g a)

end Impl

namespace Free

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
variable {α : Type u} {β : Type v}

/-- Substitution respects agreement of the computation and of the implementation. -/
def Agreement.subst {x y : Free C α} {g g' : Impl C D} (h : Agreement x y)
    (same : Impl.Agreement g g') : Agreement (x.subst g) (y.subst g') :=
  Agreement.casesOn (motive := fun x y _ => Agreement (x.subst g) (y.subst g')) h
    (fun {_ _} e => .pure e)
    (fun a {_ _} next => (same a).bind (fun i => (next i).subst same))

def substBind (g : Impl C D) (f : α → Free C β) :
    (x : Free C α) →
      Agreement ((x.bind f).subst g) ((x.subst g).bind (fun a => (f a).subst g))
  | .pure a => .refl ((f a).subst g)
  | .request a k =>
      ((Agreement.refl (g a)).bind (fun i => substBind g f (k i))).trans
        (bindAssoc _ _ (g a)).symm

def substId : (x : Free C α) → Agreement (x.subst (Impl.id C)) x
  | .pure _ => .pure .refl
  | .request a k => .request a (fun i => substId (k i))

def substTrans (g : Impl C D) (h : Impl D E) :
    (x : Free C α) → Agreement ((x.subst g).subst h) (x.subst (g.trans h))
  | .pure _ => .pure .refl
  | .request a k =>
      (substBind h _ (g a)).trans
        ((Agreement.refl ((g a).subst h)).bind (fun i => substTrans g h (k i)))

def runSubst (g : Impl C D) (provider : Section D) :
    (x : Free C α) → (x.subst g).run provider ≡ x.run (g.run provider)
  | .pure _ => .refl
  | .request a k =>
      (runBind provider _ (g a)).trans (runSubst g provider (k ((g a).run provider)))

/-- A computation whose calls are all pure makes no call: it returns the value of its run. -/
def substOfSection (f : Section C) :
    (x : Free C α) → Agreement (x.subst (Impl.ofSection (D := D) f)) (.pure (x.run f))
  | .pure _ => .pure .refl
  | .request a k => substOfSection f (k (f a))

end Free

namespace Impl

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
  {G : Container.{s''', p'''}}

namespace Agreement

def refl (f : Impl C D) : Agreement f f := fun a => .refl (f a)

def symm {f g : Impl C D} (h : Agreement f g) : Agreement g f := fun a => (h a).symm

def trans {f g k : Impl C D} (h : Agreement f g) (j : Agreement g k) : Agreement f k :=
  fun a => (h a).trans (j a)

end Agreement

def idTrans (f : Impl C D) : Agreement ((id C).trans f) f := fun a => Free.bindPure (f a)

def transId (f : Impl C D) : Agreement (f.trans (id D)) f := fun a => Free.substId (f a)

def transAssoc (f : Impl C D) (g : Impl D E) (h : Impl E G) :
    Agreement ((f.trans g).trans h) (f.trans (g.trans h)) :=
  fun a => Free.substTrans g h (f a)

def transCongr {f f' : Impl C D} {g g' : Impl D E} (h : Agreement f f') (k : Agreement g g') :
    Agreement (f.trans g) (f'.trans g') := fun a => (h a).subst k

def runTrans (f : Impl C D) (g : Impl D E) (provider : Section E) :
    Homotopy ((f.trans g).run provider) (f.run (g.run provider)) :=
  fun a => Free.runSubst g provider (f a)

def runCongr {f g : Impl C D} {provider provider' : Section D} (h : Agreement f g)
    (k : Homotopy provider provider') : Homotopy (f.run provider) (g.run provider') :=
  fun a => (h a).run k

end Impl

namespace Hom

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}

def toImplId (C : Container.{s, p}) : (Hom.id C).toImpl ≡ Impl.id C := .refl

def toImplTrans (f : Hom C D) (g : Hom D E) :
    (f.trans g).toImpl ≡ f.toImpl.trans g.toImpl := .refl

def toImplRun (f : Hom C D) (provider : Section D) : f.toImpl.run provider ≡ f.run provider :=
  .refl

end Hom

end Prelude.Container
