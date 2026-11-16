import Prelude.Container.Verified

/-! Interfaces with a runtime, and machines.

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
response and the runtime after it. Evidence of such a specification for a machine, and a
verified implementation, give evidence for the machine of the implementation
(`prop:prog-mealy-dep`): this is the run of a verified implementation with a provider that has
evidence. The evidence of a bind and of a substitution moves along the two laws.

A specification of an interface, with an invariant of the runtime, gives a specification of the
interface with a runtime. The evidence of a computation moves to it, and a verified
implementation gives a verified implementation with a runtime. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' s'' p'' u v r e w z w' z' v' v''

namespace Prelude.Container

/-- The interface with a runtime. A call has a runtime. Its response has the next runtime, or
the call stops with a value of `E`. -/
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
runtime, and a response has the invariant at the next runtime. -/
def DepPoly.invariant (t : DepPoly.{s, p, w, w} C) (T : R → Type w) (Z : E → Type w) :
    DepPoly.{max s r, max p r e, w, w} (C.runtime R E) where
  Pre a := T a.2 × t.Pre a.1
  Post a pre := Outcome (t.Post a.1 pre.2) T Z

/-- The evidence of a computation moves to the computation with a runtime: from the invariant
at the first runtime, the result has the condition at the returned value and the invariant at
the last runtime (`run-mealyD`). -/
def FreeDep.thread {t : DepPoly.{s, p, w, w} C} {T : R → Type w} {Z : E → Type w}
    {Q : α → Type w} {x : Free C α} (h : FreeDep t Q x) :
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
def ImplDep.thread {r : DepPoly.{s, p, w, w} C} {t : DepPoly.{s', p', w, w} D}
    {T : R → Type w} {Z : E → Type w} {f : Impl C D} (ff : ImplDep r t f) :
    ImplDep (r.invariant T Z) (t.invariant T Z) f.thread :=
  fun a pre => (ff a.1 pre.2).thread a.2 pre.1

end Prelude.Container
