import Prelude.Container.Verified

/-! Interfaces with a runtime, and machines.

The interface with a runtime has a runtime in each call. A response has the next runtime, or
the call stops with a value. A machine is a closed provider of that interface: Aberlé's
`def:mealy` with an explicit carrier, and with a stop. A computation on an interface gives a
computation on the interface with a runtime: it has the runtime at each call in sequence, and
it ends at the first call that stops. An implementation gives an implementation in the same
manner.

The run of a computation on a machine is the run of that computation with the machine as the
provider (`run-mealy`). An implementation and a machine for its calls give a machine
(`prog→mealy`). A specification of the interface with a runtime relates the runtime before a
call to the response and the runtime after it. Evidence of such a specification for a machine,
and a verified implementation, give evidence for the machine of the implementation
(`prop:prog-mealy-dep`): this is the run of a verified implementation with a provider that has
evidence.

The graph of a machine is the specification that has the response of the machine at each call.
A specification of an interface, with an invariant of the runtime, gives a specification of the
interface with a runtime, and the evidence of a computation moves to it. -/

set_option autoImplicit false
set_option genInjectivity false

universe s p s' p' u r e w

namespace Prelude.Container

/-- The interface with a runtime. A call has a runtime. Its response has the next runtime, or
the call stops with a value of `E`. -/
def runtime (C : Container.{s, p}) (R : Type r) (E : Type e) : Container.{max s r, max p r e} where
  Shape := C.Shape × R
  Pos a := E ⊕ (C.Pos a.1 × R)

/-- A machine with the runtime `R`: a closed provider of the interface with the runtime. -/
abbrev Machine (C : Container.{s, p}) (R : Type r) (E : Type e) : Type (max s p r e) :=
  Section (C.runtime R E)

variable {C : Container.{s, p}} {D : Container.{s', p'}} {R : Type r} {E : Type e} {α : Type u}

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

namespace Machine

/-- The run of a computation on a machine, from a runtime. -/
def run (m : Machine C R E) (x : Free C α) (s : R) : E ⊕ (α × R) := (x.thread s).run m

/-- An implementation and a machine for its calls give a machine. -/
def impl (f : Impl C D) (m : Machine D R E) : Machine C R E := f.thread.run m

/-- The graph of a machine: the specification that has the response of the machine at each
call. -/
def graph (m : Machine C R E) : DepPoly.{max s r, max p r e, 0, max p r e} (C.runtime R E) where
  Pre _ := PUnit
  Post a _ b := m a ≡ b

/-- A machine has evidence of its graph. -/
def graphEvidence (m : Machine C R E) : Evidence m.graph m := fun _ _ => .refl

end Machine

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

end Prelude.Container
