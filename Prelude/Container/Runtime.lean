import Prelude.Container.Verified
import Prelude.Container.Comonoid

/-!
# Interfaces with a runtime, and machines

The interface with a runtime has a runtime in each call. A response has the next runtime, or
the call stops with a value. A machine is a closed provider of that interface: Aberlé's
`def:mealy` with an explicit carrier, and with a stop. A computation on an interface gives a
computation on the interface with a runtime: it has the runtime at each call in sequence, and
it ends at the first call that stops. An implementation gives an implementation in the same
manner.

The computation with a runtime has three laws, each as an agreement. It respects agreement.
The computation of a bind is the first part with the runtime, and then the rest from the
result of the first part. The computation of a substitution is the substitution of the
implementation with a runtime. Thus the implementation with a runtime of the implementation
with one call is the implementation with one call, and that of a composite is the composite.

The run of a computation on a machine is the run of that computation with the machine as the
provider (`run-mealy`). An implementation and a machine for its calls give a machine
(`prog→mealy`). The laws of the run are the laws of the computation with a runtime at a
provider: the run of a bind, the run of a substitution on the machine of the implementation,
and the machine of a composite. The identity of the two runs from each runtime is a congruence
of computations. It has the agreement after the substitution of an implementation, at the
machine of that implementation.

A specification of the interface with a runtime relates the runtime before a call to the
response and the runtime after it. The graph of a machine is such a specification, and
`ImplDep.graph f.thread m` is the lift of `f.thread` between the graph of `m.impl f` and the
graph of `m`. Evidence of such a specification for a machine, and a
verified implementation, give evidence for the machine of the implementation
(`prop:prog-mealy-dep`): this is the run of a verified implementation with a provider that has
evidence. The evidence of a bind and of a substitution moves along the two laws.

A specification of an interface, with an invariant of the runtime, gives a specification of the
interface with a runtime. The evidence of a computation moves to it, and a verified
implementation gives a verified implementation with a runtime.

A specification of an interface is also a specification of the interface with the unit runtime
and no stop. The two have the same universe levels, and the evidence of a computation and the
evidence of the computation with the unit runtime give each other.

A lens of runtimes is a morphism of two state objects: its view gives a part of the runtime, and
its update gives the runtime with a new part. A machine on the part gives a machine on the
whole runtime along the lens. For a lawful lens, the run on the whole is the run on the part
from the view, with the update of the first runtime at the last value of the part. Thus two
computations with one run on the machine of the part have one run on each machine of the whole
that is that machine along the lens at their calls, in each continuation.

The interface of a cell is Aberlé's `State`: a read and a write. Its machine has the value as
the runtime (`state-mealy`). The five equations of global state hold on it by computation. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v r e w z w' z' v' v''

namespace Prelude.Container

/-- The interface with a runtime. A call has a runtime. Its response has the next runtime, or
the call stops with a value of `E`. The runtime, the stop, the shapes, and the positions have
independent universe levels. -/
def runtime (C : Container.{s, p}) (R : Type r) (E : Type e) : Container.{max s r, max p r e} where
  Shape := C.Shape × R
  Pos a := E ⊕ (C.Pos a.1 × R)

/-- A machine with the runtime `R`: a closed provider of the interface with the runtime. -/
abbrev Machine (C : Container.{s, p}) (R : Type r) (E : Type e) : Type (max s p r e) :=
  Section (C.runtime R E)

variable {C : Container.{s, p}} {D : Container.{s', p'}} {G : Container.{s'', p''}}
  {R : Type r} {E : Type e} {α : Type u} {β : Type v}

/-- The computation with the runtime at each call. A response gives the next runtime to the
rest, and a stop ends the computation. The result has the returned value and the last runtime,
or the value of the stop. -/
def Free.thread : Free C α → R → Free (C.runtime R E) (E ⊕ (α × R))
  | .pure a, s => .pure (.inr (a, s))
  | .request a k, s =>
      .request (a, s)
        (Sum.elim (fun stopped => .pure (.inl stopped)) (fun next => thread (k next.1) next.2))

/-- The implementation with the runtime at each call. -/
def Impl.thread (f : Impl C D) : Impl (C.runtime R E) (D.runtime R E) :=
  fun a => (f a.1).thread a.2

namespace Free

/-- The rest of a computation with a runtime, from an earlier result. A stop ends the
computation, and a returned value gives its runtime to the rest. -/
def resume (f : α → Free C β) : E ⊕ (α × R) → Free (C.runtime R E) (E ⊕ (β × R)) :=
  Sum.elim (fun stopped => .pure (.inl stopped)) (fun result => (f result.1).thread result.2)

/-- The computation with a runtime of a call has the rest at each response. The identity holds
by computation. -/
def threadRequest (a : C.Shape) (k : C.Pos a → Free C α) (s : R) :
    (Free.request a k).thread (E := E) s ≡ .request (a, s) (resume k) :=
  .refl

/-- The computation with a runtime respects agreement. -/
def Agreement.thread {x y : Free C α} (h : Agreement x y) :
    (s : R) → Agreement (x.thread (E := E) s) (y.thread s) :=
  Agreement.casesOn
    (motive := fun x y _ => (s : R) → Agreement (x.thread (E := E) s) (y.thread s)) h
    (fun {_ _} same s => .pure (Identity.cong (fun a => Sum.inr (a, s)) same))
    (fun a {k k'} next s =>
      Agreement.request (C := C.runtime R E) (shape := (a, s)) (k := resume k) (k' := resume k')
        fun b =>
        Sum.casesOn (motive := fun b => Agreement (resume (E := E) k b) (resume k' b)) b
          (fun _ => .pure .refl) (fun result => (next result.1).thread result.2))

/-- The computation with a runtime of a bind: the first part with the runtime, and then the
rest from its result. -/
def threadBind (f : α → Free C β) : (x : Free C α) → (s : R) →
    Agreement ((x.bind f).thread (E := E) s) ((x.thread s).bind (resume f))
  | .pure a, s => .refl ((f a).thread s)
  | .request a k, s =>
      Agreement.request (C := C.runtime R E) (shape := (a, s))
        (k := resume fun i => (k i).bind f) (k' := fun b => (resume k b).bind (resume f))
        fun b =>
        Sum.casesOn
          (motive := fun b =>
            Agreement (resume (E := E) (fun i => (k i).bind f) b)
              ((resume k b).bind (resume f)))
          b (fun _ => .pure .refl) (fun result => threadBind f (k result.1) result.2)

/-- The computation with a runtime of a substitution: the substitution of the implementation
with a runtime. -/
def threadSubst (g : Impl C D) : (x : Free C α) → (s : R) →
    Agreement ((x.subst g).thread (E := E) s) ((x.thread s).subst g.thread)
  | .pure _, _ => .pure .refl
  | .request a k, s =>
      (threadBind (fun i => (k i).subst g) (g a) s).trans
        (Agreement.bind (.refl ((g a).thread s)) fun b =>
          Sum.casesOn
            (motive := fun b =>
              Agreement (resume (E := E) (fun i => (k i).subst g) b)
                ((resume k b).subst g.thread))
            b (fun _ => .pure .refl) (fun result => threadSubst g (k result.1) result.2))

end Free

namespace Impl

/-- The implementation with a runtime respects agreement. -/
def Agreement.thread {f g : Impl C D} (h : Agreement f g) :
    Agreement (f.thread (R := R) (E := E)) g.thread :=
  fun a => (h a.1).thread a.2

/-- The implementation with one call, with a runtime, is the implementation with one call. -/
def threadId (C : Container.{s, p}) :
    Agreement ((Impl.id C).thread (R := R) (E := E)) (Impl.id (C.runtime R E)) :=
  fun a =>
    Free.Agreement.request (C := C.runtime R E) (shape := a) (k := Free.resume Free.pure)
      (k' := Free.pure) fun b =>
      Sum.casesOn
        (motive := fun b => Free.Agreement (Free.resume (C := C) (E := E) Free.pure b) (.pure b))
        b
        (fun _ => .pure .refl) (fun _ => .pure .refl)

/-- A composite with a runtime is the composite of the two implementations with a runtime. -/
def threadTrans (f : Impl C D) (g : Impl D G) :
    Agreement ((f.trans g).thread (R := R) (E := E)) (f.thread.trans g.thread) :=
  fun a => Free.threadSubst g (f a.1) a.2

end Impl

namespace Machine

/-- The run of a computation on a machine, from a runtime. -/
def run (m : Machine C R E) (x : Free C α) (s : R) : E ⊕ (α × R) := (x.thread s).run m

/-- An implementation and a machine for its calls give a machine. -/
def impl (f : Impl C D) (m : Machine D R E) : Machine C R E := f.thread.run m

/-- The result of a run, from an earlier result. A stop stays, and a returned value gives its
runtime to the run of the rest. -/
def resume (m : Machine C R E) (f : α → Free C β) : E ⊕ (α × R) → E ⊕ (β × R) :=
  Sum.elim .inl (fun result => m.run (f result.1) result.2)

/-- Computations that agree have one run on machines that agree. -/
def runCongr {m m' : Machine C R E} {x y : Free C α} (h : Free.Agreement x y)
    (same : Homotopy m m') (s : R) : m.run x s ≡ m'.run y s :=
  (h.thread s).run same

/-- The run of a bind: the run of the rest from the result of the first part. -/
def runBind (m : Machine C R E) (f : α → Free C β) (x : Free C α) (s : R) :
    m.run (x.bind f) s ≡ m.resume f (m.run x s) :=
  ((Free.threadBind f x s).run (Homotopy.refl m)).trans
    ((Free.runBind m (Free.resume f) (x.thread s)).trans
      (Sum.casesOn (motive := fun b => (Free.resume f b).run m ≡ m.resume f b) (m.run x s)
        (fun _ => .refl) (fun _ => .refl)))

/-- The run of a substitution on a machine is the run on the machine of the implementation. -/
def runSubst (g : Impl C D) (m : Machine D R E) (x : Free C α) (s : R) :
    m.run (x.subst g) s ≡ (m.impl g).run x s :=
  ((Free.threadSubst g x s).run (Homotopy.refl m)).trans (Free.runSubst g.thread m (x.thread s))

/-- The congruence of a machine: two computations have one run from each runtime. -/
def congruence (m : Machine C R E) : Free.Congruence.{s, p, u, max r e u} C α where
  Rel x y := (s : R) → m.run x s ≡ m.run y s
  agree h s := runCongr h (Homotopy.refl m) s
  symm h s := (h s).symm
  trans h k s := (h s).trans (k s)
  request a k k' next s :=
    Sum.casesOn
      (motive := fun b => (Free.resume (E := E) k b).run m ≡ (Free.resume k' b).run m)
      (m (a, s)) (fun _ => .refl) (fun result => next result.1 result.2)

/-- Computations that agree after the substitution of an implementation have one run on the
machine of the implementation. -/
def runOfSubst (g : Impl C D) (m : Machine D R E) {x y : Free C α}
    (h : (Free.Congruence.subst g).Rel x y) : (m.impl g).congruence.Rel x y :=
  fun s => (runSubst g m x s).symm.trans ((runCongr h (Homotopy.refl m) s).trans (runSubst g m y s))

/-- Implementations that agree give one machine from machines that agree. -/
def implCongr {f g : Impl C D} {m m' : Machine D R E} (h : Impl.Agreement f g)
    (same : Homotopy m m') : Homotopy (m.impl f) (m'.impl g) :=
  fun a => runCongr (h a.1) same a.2

/-- The machine of the implementation with one call is the machine. -/
def implId (m : Machine C R E) : Homotopy (m.impl (Impl.id C)) m :=
  fun a => (Impl.threadId C a).run (Homotopy.refl m)

/-- The machine of a composite is the machine of the first implementation, on the machine of
the second implementation. -/
def implTrans (f : Impl C D) (g : Impl D G) (m : Machine G R E) :
    Homotopy (m.impl (f.trans g)) ((m.impl g).impl f) :=
  fun a => runSubst g m (f a.1) a.2

end Machine

namespace FreeDep

variable {t : DepPoly.{max s r, max p r e, w, z} (C.runtime R E)}

/-- The evidence of a bind with a runtime: the evidence of the first part, and the evidence of
the rest from each result, which receives the evidence at that result. -/
def threadBind {F : E ⊕ (α × R) → Type v'} {F' : E ⊕ (β × R) → Type v''} {f : α → Free C β}
    {x : Free C α} {s : R} (h : FreeDep t F (x.thread s))
    (k : (b : E ⊕ (α × R)) → F b → FreeDep t F' (Free.resume f b)) :
    FreeDep t F' ((x.bind f).thread s) :=
  (h.bind k).reindex (Free.threadBind f x s).symm

/-- The evidence of a substitution with a runtime, for a verified implementation with a
runtime. -/
def threadSubst {t' : DepPoly.{max s' r, max p' r e, w', z'} (D.runtime R E)} {g : Impl C D}
    (gg : ImplDep t t' g.thread) {F : E ⊕ (α × R) → Type v'} {x : Free C α} {s : R}
    (h : FreeDep t F (x.thread s)) : FreeDep t' F ((x.subst g).thread s) :=
  (h.subst gg).reindex (Free.threadSubst g x s).symm

end FreeDep

/-- The condition at the result of a computation with a runtime, from a condition at the
returned value, an invariant of the runtime, and a condition at a stop. -/
def Outcome (Q : α → Type w) (T : R → Type w) (Z : E → Type w) : E ⊕ (α × R) → Type w
  | .inl stopped => Z stopped
  | .inr result => Q result.1 × T result.2

/-- The specification of the interface with a runtime, from a specification of the interface,
an invariant of the runtime, and a condition at a stop. A call has the invariant at its
runtime, and a response has the invariant at the next runtime. The precondition and the
postcondition of the specification have independent universe levels. The invariant and the
condition at a stop have the level of the postcondition. -/
def DepPoly.invariant (t : DepPoly.{s, p, w, z} C) (T : R → Type z) (Z : E → Type z) :
    DepPoly.{max s r, max p r e, max w z, z} (C.runtime R E) where
  Pre a := T a.2 × t.Pre a.1
  Post a pre := Outcome (t.Post a.1 pre.2) T Z

/-- The evidence of a computation moves to the computation with a runtime: from the invariant
at the first runtime, the result has the condition at the returned value and the invariant at
the last runtime (`run-mealyD`). -/
def FreeDep.thread {t : DepPoly.{s, p, w, z} C} {T : R → Type z} {Z : E → Type z}
    {Q : α → Type z} {x : Free C α} (h : FreeDep t Q x) :
    (s : R) → T s → FreeDep (t.invariant T Z) (Outcome Q T Z) (x.thread s) :=
  FreeDep.casesOn
    (motive := fun x _ => (s : R) → T s → FreeDep (t.invariant T Z) (Outcome Q T Z) (x.thread s))
    h
    (fun q _ inv => .pure (q, inv))
    (fun {a k} pre verified s inv =>
      FreeDep.request (r := t.invariant T Z) (shape := (a, s))
        (next := Sum.elim (fun stopped => .pure (.inl stopped))
          (fun next => (k next.1).thread next.2))
        (inv, pre)
        fun b =>
          Sum.casesOn
            (motive := fun b => (t.invariant T Z).Post (a, s) (inv, pre) b →
              FreeDep (t.invariant T Z) (Outcome Q T Z)
                (Sum.elim (fun stopped => Free.pure (.inl stopped))
                  (fun next => (k next.1).thread next.2) b))
            b (fun _ post => .pure post)
            (fun next post => (verified next.1 post.1).thread next.2 post.2))

/-- A verified implementation gives a verified implementation with a runtime, for an invariant
of the runtime. -/
def ImplDep.thread {r : DepPoly.{s, p, w, z} C} {t : DepPoly.{s', p', w', z} D}
    {T : R → Type z} {Z : E → Type z} {f : Impl C D} (ff : ImplDep r t f) :
    ImplDep (r.invariant T Z) (t.invariant T Z) f.thread :=
  fun a pre => (ff a.1 pre.2).thread a.2 pre.1

/-- The condition at a result with the unit runtime and no stop, from a condition at the
returned value. -/
def Still (Q : α → Type v) : Empty ⊕ (α × PUnit.{1}) → Type v
  | .inl e => nomatch e
  | .inr y => Q y.1

/-- The specification with the unit runtime and no stop, from a specification with no runtime.
The precondition and the postcondition keep their universe levels. -/
def DepPoly.still (t : DepPoly.{s, p, w, z} C) :
    DepPoly.{s, p, w, z} (C.runtime PUnit.{1} Empty) where
  Pre a := t.Pre a.1
  Post a pre := Still (t.Post a.1 pre)

/-- The evidence of a computation with the unit runtime gives the evidence of the
computation. -/
def FreeDep.ofStill {t : DepPoly.{s, p, w, z} C} {Q : α → Type v} : (x : Free C α) →
    FreeDep (DepPoly.still t) (Still Q) (x.thread PUnit.unit) → FreeDep t Q x
  | .pure _, h => .pure h.result
  | .request _ k, h =>
      .request h.parts.1 fun i post => ofStill (k i) (h.parts.2 (.inr (i, .unit)) post)

/-- The evidence of a computation gives the evidence of the computation with the unit
runtime. -/
def FreeDep.toStill {t : DepPoly.{s, p, w, z} C} {Q : α → Type v} : (x : Free C α) →
    FreeDep t Q x → FreeDep (DepPoly.still t) (Still Q) (x.thread PUnit.unit)
  | .pure _, h => .pure h.result
  | .request a k, h =>
      FreeDep.request (r := DepPoly.still t) (shape := (a, PUnit.unit))
        (next := Sum.elim (fun stopped => .pure (.inl stopped))
          (fun next => (k next.1).thread next.2))
        h.parts.1
        fun i =>
          match i with
          | .inl e => nomatch e
          | .inr y => fun post => toStill (k y.1) (h.parts.2 y.1 post)

section Lens

variable {A : Type w}

/-- The result on the whole runtime, from a result on a part: a stop stays, and the last
runtime is the update of the runtime `s` with the last value of the part. -/
def Hom.updateResult (ℓ : Hom (state R) (state A)) (s : R) : E ⊕ (α × A) → E ⊕ (α × R) :=
  Sum.map _root_.id fun b => (b.1, ℓ.position s b.2)

/-- Two runtimes with one update at each value give one result. -/
def Hom.updateResultCongr (ℓ : Hom (state R) (state A)) {s s' : R}
    (same : (a : A) → ℓ.position s a ≡ ℓ.position s' a) :
    (out : E ⊕ (α × A)) → ℓ.updateResult s out ≡ ℓ.updateResult s' out
  | .inl _ => .refl
  | .inr b => Identity.cong (fun t => Sum.inr (b.1, t)) (same b.2)

namespace Machine

/-- A machine on a part of the runtime gives a machine on the whole runtime, along a lens: a
call has the view of the runtime, and the next runtime is the update. -/
def along (ℓ : Hom (state R) (state A)) (μ : Machine C A E) : Machine C R E :=
  fun a => ℓ.updateResult a.2 (μ (a.1, ℓ.shape a.2))

/-- The run on the whole runtime is the run on the part from the view, with the update of the
first runtime at the last value of the part. A return uses the counit square of the lens, and a
call uses its comultiplication square. -/
def runAlong {ℓ : Hom (state R) (state A)} (law : ℓ.Lawful) (μ : Machine C A E) :
    (x : Free C α) → (s : R) →
      (μ.along ℓ).run x s ≡ ℓ.updateResult s (μ.run x (ℓ.shape s))
  | .pure v, s => Identity.cong (fun t => Sum.inr (v, t)) (law.updateView s).symm
  | .request d k, s =>
      Sum.casesOn
        (motive := fun out =>
          (Free.resume k (ℓ.updateResult s out)).run (μ.along ℓ) ≡
            ℓ.updateResult s ((Free.resume k out).run μ))
        (μ (d, ℓ.shape s))
        (fun _ => .refl)
        (fun b =>
          (runAlong law μ (k b.1) (ℓ.position s b.2)).trans
            ((Identity.cong
                (fun a => ℓ.updateResult (ℓ.position s b.2) (μ.run (k b.1) a))
                (law.viewUpdate s b.2)).trans
              (ℓ.updateResultCongr (fun c => law.updateUpdate s b.2 c) (μ.run (k b.1) b.2))))

/-- Two computations with one run on the machine of a part have one run on a machine of the
whole runtime, after an implementation and in each continuation. At the calls of the
implementation, the machine of the whole is the machine of the part along a lawful lens. -/
def alongCongr {ℓ : Hom (state R) (state A)} (law : ℓ.Lawful) (μ : Machine C A E)
    (c : Impl C D) (m : Machine D R E) (same : Homotopy (m.impl c) (μ.along ℓ))
    {x y : Free C β} (h : (a : A) → μ.run x a ≡ μ.run y a) (k : β → Free D α) (s : R) :
    m.run ((x.subst c).bind k) s ≡ m.run ((y.subst c).bind k) s :=
  let part (z : Free C β) :
      m.run (z.subst c) s ≡ ℓ.updateResult s (μ.run z (ℓ.shape s)) :=
    (runSubst c m z s).trans
      ((runCongr (Free.Agreement.refl z) same s).trans (runAlong law μ z s))
  let whole : m.run (x.subst c) s ≡ m.run (y.subst c) s :=
    (part x).trans ((Identity.cong (ℓ.updateResult s) (h (ℓ.shape s))).trans (part y).symm)
  (runBind m k (x.subst c) s).trans
    ((Identity.cong (m.resume k) whole).trans (runBind m k (y.subst c) s).symm)

end Machine

end Lens

/-- The calls of a cell: a read, and a write of a value. -/
inductive CellOp (A : Type u) : Type u where
  | get
  | put (a : A)

/-- The interface of a cell: a read has the value as its response, and a write has one
response. -/
def cell (A : Type u) : Container.{u, u} where
  Shape := CellOp A
  Pos
    | .get => A
    | .put _ => PUnit

/-- The machine of a cell, with the value as the runtime. A read gives the value, and a write
replaces it. The machine does not stop. -/
def Machine.cell (A : Type u) (E : Type e) : Machine (cell A) A E
  | (.get, a) => .inr (a, a)
  | (.put b, _) => .inr (⟨⟩, b)

namespace cell

variable (A : Type u) (E : Type e)

/-- Two reads give one value. -/
def getGet (k : A → A → Free (cell A) β) (a : A) :
    (Machine.cell A E).run (.request .get fun x => .request .get fun y => k x y) a ≡
      (Machine.cell A E).run (.request .get fun x => k x x) a :=
  .refl

/-- A read whose value has no use does nothing. -/
def getDiscard (x : Free (cell A) β) (a : A) :
    (Machine.cell A E).run (.request .get fun _ => x) a ≡ (Machine.cell A E).run x a :=
  .refl

/-- Of two writes, the last one stays. -/
def putPut (v w : A) (x : Free (cell A) β) (a : A) :
    (Machine.cell A E).run (.request (.put v) fun _ => .request (.put w) fun _ => x) a ≡
      (Machine.cell A E).run (.request (.put w) fun _ => x) a :=
  .refl

/-- A read and then a write of its value does nothing. -/
def getPut (x : Free (cell A) β) (a : A) :
    (Machine.cell A E).run (.request .get fun v => .request (.put v) fun _ => x) a ≡
      (Machine.cell A E).run x a :=
  .refl

/-- A write and then a read gives the written value. -/
def putGet (v : A) (k : A → Free (cell A) β) (a : A) :
    (Machine.cell A E).run (.request (.put v) fun _ => .request .get k) a ≡
      (Machine.cell A E).run (.request (.put v) fun _ => k v) a :=
  .refl

end cell

end Prelude.Container
