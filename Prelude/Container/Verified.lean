import Prelude.Container.Free

/-!
# Verified computations and implementations

Evidence that a computation satisfies a specification of its interface, and verified
implementations. This is Aberlé's `FreeDep` with `>>=Dep`, `FreeDep⇒`, `∘Dep`, and `compDep`.
The evidence has a witness of the precondition at each call. Its continuation receives the
evidence of the postcondition of the response, for that witness. A run with a provider that
satisfies the specification gives the evidence at the returned value.

The evidence of a composite is indexed by the composite of the implementations, so the
composition of evidence follows the constructors of the composition of implementations.

A computation has runs along its evidence: a run has a response of each call with its
postcondition, and the result. An implementation has a specification from a specification of
its calls. A witness of its precondition has a witness of the precondition of each call that a
run can make, and its postcondition has the runs along that witness. The implementation is
verified for it, and each specification with a lift of the implementation maps to it. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v w z w' z' w'' z'' u' v' i

namespace Prelude.Container

/-- Evidence of `Q` at each value that a computation returns, with the specification `r` as
the assumption on each call. Its constructors follow the constructors of the computation. The
universe levels of the specification and of `Q` are independent. -/
inductive FreeDep {C : Container.{s, p}} (r : DepPoly.{s, p, w, z} C) {α : Type u}
    (Q : α → Type v) : Free C α → Type (max s p u v w z) where
  /-- The evidence at a returned value. -/
  | pure {value : α} (result : Q value) : FreeDep r Q (.pure value)
  /-- A witness of the precondition of a call, and the evidence of the continuation at each
  response, which receives the evidence of the postcondition for that witness. -/
  | request {shape : C.Shape} {next : C.Pos shape → Free C α} (pre : r.Pre shape)
      (verified : (i : C.Pos shape) → r.Post shape pre i → FreeDep r Q (next i)) :
      FreeDep r Q (.request shape next)

namespace FreeDep

variable {C : Container.{s, p}} {r : DepPoly.{s, p, w, z} C} {α : Type u} {β : Type u'}
  {Q : α → Type v} {R : β → Type v'}

/-- One call with a witness of its precondition. The response has the evidence of its
postcondition. -/
def call (a : C.Shape) (pre : r.Pre a) : FreeDep r (r.Post a pre) (Free.call a) :=
  .request pre (fun _ post => .pure post)

/-- Continue each returned value with a verified computation that receives the evidence at
that value. -/
def bind {f : α → Free C β} {x : Free C α} (h : FreeDep r Q x)
    (k : (a : α) → Q a → FreeDep r R (f a)) : FreeDep r R (x.bind f) :=
  FreeDep.casesOn (motive := fun x _ => FreeDep r R (x.bind f)) h
    (fun {a} q => k a q)
    (fun {_ _} pre next => .request pre (fun i post => (next i post).bind k))

/-- The evidence at the value that a run returns. The provider gives the evidence of each
postcondition. -/
def run {provider : Section C} (e : Evidence r provider) {x : Free C α} (h : FreeDep r Q x) :
    Q (x.run provider) :=
  FreeDep.casesOn (motive := fun x _ => Q (x.run provider)) h
    (fun q => q)
    (fun {a k} pre verified => run e (x := k (provider a)) (verified (provider a) (e a pre)))

/-- The run of a bind gives the evidence of the run of the continuation, across the identity
of the two returned values. -/
def runBind {provider : Section C} (e : Evidence r provider) {f : α → Free C β}
    (k : (a : α) → Q a → FreeDep r R (f a)) {x : Free C α} (h : FreeDep r Q x) :
    Identity.transport R (Free.runBind provider f x) ((h.bind k).run e) ≡
      (k (x.run provider) (h.run e)).run e :=
  FreeDep.casesOn
    (motive := fun x h =>
      Identity.transport R (Free.runBind provider f x) ((h.bind k).run e) ≡
        (k (x.run provider) (h.run e)).run e)
    h
    (fun _ => .refl)
    (fun {a _} pre verified => runBind e k (verified (provider a) (e a pre)))

/-- A computation has evidence for the graph of a provider: it returns the value of its run
with that provider. -/
def graph (f : Section C) : (x : Free C α) → FreeDep f.graph (fun b => x.run f ≡ b) x
  | .pure _ => .pure .refl
  | .request a k =>
      .request ⟨⟩ fun _ same =>
        Identity.ind (fun j _ => FreeDep f.graph (fun b => (k (f a)).run f ≡ b) (k j))
          (graph f (k (f a))) same

/-- The type of the evidence at a returned value. -/
def ResultAt (Q : α → Type v) : Free C α → Type v
  | .pure a => Q a
  | .request _ _ => PUnit

/-- The evidence at a returned value. -/
def result {x : Free C α} (h : FreeDep r Q x) : ResultAt Q x :=
  FreeDep.casesOn (motive := fun x _ => ResultAt Q x) h (fun q => q) (fun _ _ => ⟨⟩)

/-- The type of the two parts of the evidence at a call. -/
def PartsAt (r : DepPoly.{s, p, w, z} C) (Q : α → Type v) :
    Free C α → Type (max s p u v w z)
  | .pure _ => PUnit
  | .request a k => (pre : r.Pre a) × ((i : C.Pos a) → r.Post a pre i → FreeDep r Q (k i))

/-- The witness of the precondition of a call, and the evidence of its continuation. -/
def parts {x : Free C α} (h : FreeDep r Q x) : PartsAt r Q x :=
  FreeDep.casesOn (motive := fun x _ => PartsAt r Q x) h (fun _ => ⟨⟩)
    (fun pre verified => ⟨pre, verified⟩)

/-- Evidence for the specification that admits no call gives the value that the computation
returns. The computation agrees with the computation that returns that value, and the value
has the condition. -/
def returned {x : Free C α} (h : FreeDep (DepPoly.noCall.{s, p, w, z} C) Q x) :
    (value : α) × (Free.Agreement x (.pure value) × Q value) :=
  FreeDep.casesOn
    (motive := fun x _ => (value : α) × (Free.Agreement x (.pure value) × Q value)) h
    (fun {value} q => ⟨value, .pure .refl, q⟩)
    (fun pre _ => nomatch pre)

/-- A computation that makes no call gives its value to the continuation. -/
def returnedBind {x : Free C α} (h : FreeDep (DepPoly.noCall.{s, p, w, z} C) Q x)
    (k : α → Free C β) : Free.Agreement (x.bind k) (k h.returned.1) :=
  h.returned.2.1.bind (fun i => .refl (k i))

/-- Evidence moves along an agreement of computations. An identity of two returned values
moves the evidence at the first value to the second value. -/
def reindex {x y : Free C α} (agree : Free.Agreement x y) : FreeDep r Q x → FreeDep r Q y :=
  Free.Agreement.casesOn (motive := fun x y _ => FreeDep r Q x → FreeDep r Q y) agree
    (fun {_ _} same h => .pure (Identity.transport Q same h.result))
    (fun _ {_ _} next h =>
      .request h.parts.1 (fun i post => reindex (next i) (h.parts.2 i post)))

/-- The run of moved evidence is the evidence of the first run, across the identity of the
two returned values. -/
def runReindex {provider : Section C} (e : Evidence r provider) {x y : Free C α}
    (agree : Free.Agreement x y) : (h : FreeDep r Q x) →
      Identity.transport Q (agree.run (Homotopy.refl provider)) (h.run e) ≡
        (h.reindex agree).run e :=
  Free.Agreement.casesOn
    (motive := fun x _ agree => (h : FreeDep r Q x) →
      Identity.transport Q (agree.run (Homotopy.refl provider)) (h.run e) ≡
        (h.reindex agree).run e)
    agree
    (fun {_ _} _ h => match h with
      | .pure _ => .refl)
    (fun a {_ _} next h => match h with
      | .request pre verified =>
        (Identity.cong
          (fun path => Identity.transport Q path ((verified (provider a) (e a pre)).run e))
          (Identity.transRefl ((next (provider a)).run (Homotopy.refl provider)))).trans
          (runReindex e (next (provider a)) (verified (provider a) (e a pre))))

/-- The runs of a computation along its evidence. A run of a returned value is the identity of
that value and the result. A run of a call has a response with its postcondition, and a run of
the continuation at that response. -/
def Runs : (x : Free C α) → FreeDep r Q x → α → Type (max p z u)
  | .pure a, _, o => ULift.{max p z} (a ≡ o)
  | .request s k, h, o =>
      (i : C.Pos s) × (post : r.Post s h.parts.1 i) × Runs (k i) (h.parts.2 i post) o

/-- A run under the graph of a provider ends at the value of running the computation on it. -/
def graphResult (f : Section C) : (x : Free C α) → (h : FreeDep f.graph Q x) →
    {o : α} → Runs x h o → x.run f ≡ o
  | .pure _, _, _, run => run.down
  | .request _ k, h, _, ⟨i, same, tail⟩ =>
      (Identity.cong (fun v => (k v).run f) same).trans
        (graphResult f (k i) (h.parts.2 i same) tail)

/-- The condition at the result of a run along the evidence. -/
def atRun : (x : Free C α) → (h : FreeDep r Q x) → {o : α} → Runs x h o → Q o
  | .pure _, h, _, e => Identity.transport Q e.down h.result
  | .request _ k, h, _, ⟨i, post, tail⟩ => atRun (k i) (h.parts.2 i post) tail

/-- The evidence of another condition, from a map of the conditions. -/
def mapQ {Q' : α → Type v'} (g : (a : α) → Q a → Q' a) :
    (x : Free C α) → FreeDep r Q x → FreeDep r Q' x
  | .pure a, h => .pure (g a h.result)
  | .request _ k, h => .request h.parts.1 fun i post => mapQ g (k i) (h.parts.2 i post)

/-- A computation with evidence has the evidence of its own runs. -/
def own : (x : Free C α) → (h : FreeDep r Q x) → FreeDep r (fun o => Runs x h o) x
  | .pure _, _ => .pure ⟨.refl⟩
  | .request s k, h =>
      .request h.parts.1 fun i post =>
        mapQ (Q := fun o => Runs (k i) (h.parts.2 i post) o)
          (Q' := fun o => Runs (.request s k) h o)
          (fun _ run => ⟨i, post, run⟩) (k i) (own (k i) (h.parts.2 i post))

/-- The runs do not use the condition at the result. -/
def runsOfMap {Q' : α → Type v'} (g : (a : α) → Q a → Q' a) :
    (x : Free C α) → (h : FreeDep r Q x) → {o : α} → Runs x (mapQ g x h) o → Runs x h o
  | .pure _, _, _, e => e
  | .request _ k, h, _, t => ⟨t.1, t.2.1, runsOfMap g (k t.1) (h.parts.2 t.1 t.2.1) t.2.2⟩

end FreeDep

/-- The dependent lift of an implementation. For each shape and each witness of its
precondition in `r`, the computation gives the postcondition of its response, with `t` as the
assumption on the calls. An implementation with its lift is a verified implementation. -/
def ImplDep {C : Container.{s, p}} {D : Container.{s', p'}} (r : DepPoly.{s, p, w, z} C)
    (t : DepPoly.{s', p', w', z'} D) (f : Impl C D) : Type (max s p s' p' w z w' z') :=
  (a : C.Shape) → (pre : r.Pre a) → FreeDep t (r.Post a pre) (f a)

/-- A specification map verifies the identity implementation, which makes one call. The call
has the mapped witness, and the response has the evidence that the map takes back. -/
def DepPoly.Map.toImplDep {C : Container.{s, p}} {P : DepPoly.{s, p, w, z} C}
    {Q : DepPoly.{s, p, w', z'} C} (f : P.Map Q) : ImplDep P Q (Impl.id C) :=
  fun a pre => .request (f a pre).1 fun o post => .pure ((f a pre).2 o post)

/-- The admission and response map of a verified identity implementation. -/
def ImplDep.toMap {C : Container.{s, p}} {P : DepPoly.{s, p, w, z} C}
    {Q : DepPoly.{s, p, w', z'} C} (f : ImplDep P Q (Impl.id C)) : P.Map Q :=
  fun a pre => ⟨(f a pre).parts.1, fun o post => ((f a pre).parts.2 o post).result⟩

namespace FreeDep

variable {C : Container.{s, p}} {D : Container.{s', p'}} {r : DepPoly.{s, p, w, z} C}
  {t : DepPoly.{s', p', w', z'} D} {α : Type u} {Q : α → Type v} {g : Impl C D}

/-- Replace each call with its verified implementation. -/
def subst (gg : ImplDep r t g) {x : Free C α} (h : FreeDep r Q x) : FreeDep t Q (x.subst g) :=
  FreeDep.casesOn (motive := fun x _ => FreeDep t Q (x.subst g)) h
    (fun q => .pure q)
    (fun {a _} pre verified => (gg a pre).bind (fun i post => (verified i post).subst gg))

end FreeDep

namespace ImplDep

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
  {r : DepPoly.{s, p, w, z} C} {t : DepPoly.{s', p', w', z'} D}
  {v : DepPoly.{s'', p'', w'', z''} E}

/-- The lift of the implementation with one call. -/
def id (r : DepPoly.{s, p, w, z} C) : ImplDep r r (Impl.id C) := FreeDep.call

/-- Composition in traversal order: the calls of the first lift are replaced by the second
lift. -/
def trans {f : Impl C D} {g : Impl D E} (ff : ImplDep r t f) (gg : ImplDep t v g) :
    ImplDep r v (f.trans g) := fun a pre => (ff a pre).subst gg

/-- The lift of a copairing that has a given lift at each index. With `trans`, this is
Aberlé's `compDep`. -/
def copair {ι : Type i} {F : ι → Container.{s, p}} {r : (i : ι) → DepPoly.{s, p, w, z} (F i)}
    {f : (i : ι) → Impl (F i) D} (ff : (i : ι) → ImplDep (r i) t (f i)) :
    ImplDep (DepPoly.sigma r) t (Impl.copair f) := fun a pre => ff a.1 a.2 pre

/-- The evidence of the closed provider that a verified implementation gives. -/
def run {f : Impl C D} (ff : ImplDep r t f) {provider : Section D} (e : Evidence t provider) :
    Evidence r (f.run provider) := fun a pre => (ff a pre).run e

/-- A lift moves along an agreement of implementations. -/
def reindex {f g : Impl C D} (agree : Impl.Agreement f g) (ff : ImplDep r t f) :
    ImplDep r t g := fun a pre => (ff a pre).reindex (agree a)

/-- A provider with evidence is a verified implementation without a call. -/
def ofEvidence {f : Section C} (e : Evidence r f) : ImplDep r t (Impl.ofSection f) :=
  fun a pre => .pure (e a pre)

/-- An implementation is a verified implementation of the graph of the provider that it
gives, with the graph of the provider of its calls as the assumption. -/
def graph (g : Impl C D) (f : Section D) : ImplDep (g.run f).graph f.graph g :=
  fun a _ => FreeDep.graph f (g a)

end ImplDep

/-- A morphism of specifications pairs the implementation with the lift over that implementation. -/
structure VerifiedImpl {C : Container.{s, p}} {D : Container.{s', p'}}
    (r : DepPoly.{s, p, w, z} C) (t : DepPoly.{s', p', w', z'} D) where
  /-- The implementation. -/
  impl : Impl C D
  /-- The lift of the implementation. -/
  verification : ImplDep r t impl

/-- Composition substitutes the second implementation and its evidence into the first. -/
def VerifiedImpl.trans {C : Container.{s, p}} {D : Container.{s', p'}} {G : Container.{s'', p''}}
    {r : DepPoly.{s, p, w, z} C} {t : DepPoly.{s', p', w', z'} D} {v : DepPoly.{s'', p'', w'', z''} G}
    (f : VerifiedImpl r t) (g : VerifiedImpl t v) : VerifiedImpl r v :=
  ⟨f.impl.trans g.impl, f.verification.trans g.verification⟩


namespace FreeDep

variable {C : Container.{s, p}} {D : Container.{s', p'}} {r : DepPoly.{s, p, w, z} C}
  {t : DepPoly.{s', p', w', z'} D} {α : Type u} {Q : α → Type v} {g : Impl C D}

/-- The run of substituted evidence is the run of the evidence with the provider of the
implementation, across the identity of the two returned values. -/
def runSubst (gg : ImplDep r t g) {provider : Section D} (e : Evidence t provider)
    {x : Free C α} (h : FreeDep r Q x) :
    Identity.transport Q (Free.runSubst g provider x) ((h.subst gg).run e) ≡ h.run (gg.run e) :=
  FreeDep.casesOn
    (motive := fun x h =>
      Identity.transport Q (Free.runSubst g provider x) ((h.subst gg).run e) ≡
        h.run (gg.run e))
    h
    (fun _ => .refl)
    (fun {a k} pre verified =>
      let first := Free.runBind provider (fun i => (k i).subst g) (g a)
      let second := Free.runSubst g provider (k ((g a).run provider))
      let whole := ((gg a pre).bind (fun i post => (verified i post).subst gg)).run e
      (Identity.transportTrans Q first second whole).trans
        ((Identity.cong (Identity.transport Q second)
          (runBind e (fun i post => (verified i post).subst gg) (gg a pre))).trans
          (runSubst gg e (verified ((g a).run provider) ((gg a pre).run e)))))

end FreeDep

namespace ImplDep

variable {C : Container.{s, p}} {D : Container.{s', p'}} {E : Container.{s'', p''}}
  {r : DepPoly.{s, p, w, z} C} {t : DepPoly.{s', p', w', z'} D}
  {v : DepPoly.{s'', p'', w'', z''} E}

/-- The evidence of a composite is the evidence of its two stages, across the identity of
the two responses. -/
def runTrans {f : Impl C D} {g : Impl D E} (ff : ImplDep r t f) (gg : ImplDep t v g)
    {provider : Section E} (e : Evidence v provider) (a : C.Shape) (pre : r.Pre a) :
    Evidence.reindex (Impl.runTrans f g provider) ((ff.trans gg).run e) a pre ≡
      ff.run (gg.run e) a pre :=
  FreeDep.runSubst gg e (ff a pre)

end ImplDep

section Specification

variable {C : Container.{s, p}} {D : Container.{s', p'}}

/-- The specification of an implementation, from a specification of its calls. A witness of
the precondition has a witness of the precondition of each call that a run can make. The
postcondition has the runs along that witness. -/
def Impl.spec (f : Impl C D) (t : DepPoly.{s', p', w', z'} D) :
    DepPoly.{s, p, max s' p' p w' z', max p' z' p} C where
  Pre a := FreeDep t (fun _ => PUnit.{1}) (f a)
  Post a pre b := FreeDep.Runs (f a) pre b

/-- An implementation is verified for its own specification. -/
def Impl.specDep (f : Impl C D) (t : DepPoly.{s', p', w', z'} D) : ImplDep (f.spec t) t f :=
  fun a pre => FreeDep.own (f a) pre

/-- Each specification with a lift of the implementation gives a witness of the precondition
of the specification of the implementation. -/
def Impl.specPre {f : Impl C D} {t : DepPoly.{s', p', w', z'} D} {q : DepPoly.{s, p, w, z} C}
    (ff : ImplDep q t f) (a : C.Shape) (pre : q.Pre a) : (f.spec t).Pre a :=
  FreeDep.mapQ (fun _ _ => PUnit.unit) (f a) (ff a pre)

/-- Each run along that witness has the postcondition of the specification with the lift. -/
def Impl.specPost {f : Impl C D} {t : DepPoly.{s', p', w', z'} D} {q : DepPoly.{s, p, w, z} C}
    (ff : ImplDep q t f) (a : C.Shape) (pre : q.Pre a) (b : C.Pos a)
    (run : (f.spec t).Post a (Impl.specPre ff a pre) b) : q.Post a pre b :=
  FreeDep.atRun (f a) (ff a pre) (FreeDep.runsOfMap (fun _ _ => PUnit.unit) (f a) (ff a pre) run)

/-- A verified implementation maps its interface specification to the specification of its calls
composed according to the implementation. -/
def Impl.specMap {f : Impl C D} {t : DepPoly.{s', p', w', z'} D} {q : DepPoly.{s, p, w, z} C}
    (ff : ImplDep q t f) : q.Map (f.spec t) :=
  fun a pre => ⟨Impl.specPre ff a pre, Impl.specPost ff a pre⟩

end Specification

end Prelude.Container
