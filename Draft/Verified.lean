import Draft.Diagram

/-! Verified diagrams.

A diagram is an implementation of its own interface by calls of the interface of its signature.
The interface of a diagram has one operation: a shape is the values of the context, and a
position is an exit with its values. A specification of a diagram is a dependent polynomial on
that interface, and a verified diagram is the implementation with its lift.

The function meaning of a diagram has the remaining computation as an argument, and the
evidence of a diagram has the same form. At the values of the context, and for a postcondition
at each exit: when the remaining computation has evidence at each exit with its postcondition,
the computation of the diagram has evidence. The computation at the limit of a loop has
evidence as an argument.

The evidence of a diagram is built by the constructors of the diagram:

- an exit has its postcondition;
- a step has a witness of the precondition of its operation, and the diagram of each response
  receives the postcondition of the response;
- a composite has a condition at the boundary of its continuation, which the first diagram
  establishes at each exit to that boundary, and which the continuation receives;
- a copairing has the evidence of the diagram of its case;
- a frame has a condition at the exit of its diagram, which the continuation receives with
  the case of the bypass and the kept values;
- a loop has an invariant at its entrance, which the body establishes at each exit to the
  entrance.

The lift of a diagram for a specification has the evidence at each context with a witness of
the precondition, for the postcondition of that witness. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z p w'

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type}

/-- The interface of a diagram: a shape is the values of its context, and a position is an
exit with its values. -/
def Diagram.interface (X : Ty → Type) (Γ : List Ty) (Qs : Exits Ty) : Container.{0, 0} :=
  ⟨All X Γ, fun _ => Qs.At X⟩

/-- The interface of a continuation: a shape is a case of its boundary with its values, and a
position is an exit with its values. -/
def Continuation.interface (X : Ty → Type) (K : Boundary Ty) (Qs : Exits Ty) : Container.{0, 0} :=
  ⟨K.At X, fun _ => Qs.At X⟩

/-- A diagram is an implementation of its interface by calls of the interface of its
signature. -/
def Diagram.impl {Γ : List Ty} {Qs : Exits Ty} (stop : Free (S.interface X) (Qs.At X)) (n : Nat)
    (d : Diagram S Γ Qs) : Impl (Diagram.interface X Γ Qs) (S.interface X) :=
  fun env => d.meaning stop n env

/-- A continuation is an implementation of its interface by calls of the interface of its
signature. -/
def Continuation.impl {K : Boundary Ty} {Qs : Exits Ty} (stop : Free (S.interface X) (Qs.At X))
    (n : Nat) (k : Continuation S K Qs) : Impl (Continuation.interface X K Qs) (S.interface X) :=
  fun a => k.run stop n a .pure

/-- The evidence of a diagram at the values of its context, for a postcondition at each exit:
the dependent form of the function meaning. The computation at the limit of a loop has
evidence. When the remaining computation has evidence at each exit with its postcondition, the
computation of the diagram has evidence. -/
abbrev Diagram.RunDep (r : DepPoly.{0, 0, w, z} (S.interface X)) {Γ : List Ty} {Qs : Exits Ty}
    (P : Qs.At X → Type p) (d : Diagram S Γ Qs) (env : All X Γ) : Type (max w z (p + 1)) :=
  {α : Type} → {F : α → Type p} → {stop : Free (S.interface X) α} → FreeDep r F stop →
    (n : Nat) → {cont : Qs.At X → Free (S.interface X) α} →
    ((x : Qs.At X) → P x → FreeDep r F (cont x)) → FreeDep r F (d.run stop n env cont)

/-- The evidence of a continuation at a case with its values, for a postcondition at each
exit. -/
abbrev Continuation.RunDep (r : DepPoly.{0, 0, w, z} (S.interface X)) {K : Boundary Ty}
    {Qs : Exits Ty} (P : Qs.At X → Type p) (k : Continuation S K Qs) (a : K.At X) :
    Type (max w z (p + 1)) :=
  {α : Type} → {F : α → Type p} → {stop : Free (S.interface X) α} → FreeDep r F stop →
    (n : Nat) → {cont : Qs.At X → Free (S.interface X) α} →
    ((x : Qs.At X) → P x → FreeDep r F (cont x)) → FreeDep r F (k.run stop n a cont)

variable {r : DepPoly.{0, 0, w, z} (S.interface X)}

namespace Diagram.RunDep

variable {Γ : List Ty} {Qs : Exits Ty} {P : Qs.At X → Type p} {env : All X Γ}

/-- The evidence of an exit: its postcondition. -/
def exit (out : Qs.At (Port Γ)) (h : P (out.select env)) :
    (Diagram.exit (S := S) out).RunDep r P env :=
  fun _ _ _ done => done _ h

/-- The evidence of a step: a witness of the precondition of the operation, and the evidence of
the diagram of each response, which receives the postcondition of the response. -/
def step (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    (admit : r.Pre ⟨call.1, env.select call.2⟩)
    (next : (resp : (S.output call.1).At X) → r.Post ⟨call.1, env.select call.2⟩ admit resp →
      (rest resp.1).RunDep r P (resp.2.append env)) :
    (Diagram.step call rest).RunDep r P env :=
  fun limit n _ done => .request admit fun resp post => next resp post limit n done

/-- The evidence of a composite, for a condition at the boundary of the continuation: the
evidence of the first diagram, with that condition at each exit to the boundary, and the
evidence of the continuation at each case with the condition. -/
def seq {K : Boundary Ty} (Mid : K.At X → Type p) (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (firstDep : first.RunDep r (Exits.At.elim Mid P) env)
    (nextDep : (a : K.At X) → Mid a → next.RunDep r P a) :
    (Diagram.seq first next).RunDep r P env :=
  fun {α F _} limit n _ done =>
    firstDep limit n
      (Exits.At.elimRel
        (R := fun (A : Type p) (c : Free (S.interface X) α) => A → FreeDep r F c)
        (fun a mid => nextDep a mid limit n done) (fun x post => done x post))

end Diagram.RunDep

namespace Continuation.RunDep

variable {K : Boundary Ty} {Qs : Exits Ty} {P : Qs.At X → Type p}

/-- The evidence of a copairing: the evidence of the diagram of the case. -/
def copair {a : K.At X} (each : (c : K.Case) → Diagram S c.1 Qs)
    (dep : (each a.1).RunDep r P a.2) : (Continuation.copair each).RunDep r P a :=
  fun limit n _ done => dep limit n done

/-- The evidence of a frame, for a condition at the exit of its diagram: the evidence of the
diagram at the selected values, and the evidence of the continuation at the case of the bypass,
the kept values, and each exit with the condition. -/
def frame {M R : Boundary Ty} {Δ : List Ty} {a : R.At X} (Mid : K.At X → Type p)
    (kept : (c : R.Case) → M.At (Port c.1)) (args : (c : R.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (sharedDep : shared.RunDep r (Exits.At.only Mid) (a.2.select (args a.1)))
    (nextDep : (out : K.At X) → Mid out →
      next.RunDep r P
        ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩) :
    (Continuation.frame kept args shared next).RunDep r P a :=
  fun {α F _} limit n _ done =>
    sharedDep limit n
      (Exits.At.onlyRel
        (R := fun (A : Type p) (c : Free (S.interface X) α) => A → FreeDep r F c)
        (fun out mid => nextDep out mid limit n done))

/-- The evidence of a loop with a number of unrollings, for an invariant at the entrance. With
no unrolling it is the evidence at the limit. -/
def unrolled {α : Type} {F : α → Type p} {stop : Free (S.interface X) α}
    (limit : FreeDep r F stop) (n : Nat) (Inv : K.At X → Type p)
    {body : Continuation S K (K :: Qs)}
    (bodyDep : (a : K.At X) → Inv a → body.RunDep r (Exits.At.elim Inv P) a)
    {cont : Qs.At X → Free (S.interface X) α}
    (done : (x : Qs.At X) → P x → FreeDep r F (cont x)) :
    (m : Nat) → (a : K.At X) → Inv a →
      FreeDep r F (Continuation.unrolled stop (body.run stop n) m a cont)
  | 0, _, _ => limit
  | m + 1, a, inv =>
      bodyDep a inv limit n
        (Exits.At.elimRel
          (R := fun (A : Type p) (c : Free (S.interface X) α) => A → FreeDep r F c)
          (fun a' inv' => unrolled limit n Inv bodyDep done m a' inv')
          (fun x post => done x post))

/-- The evidence of a loop, for an invariant at the entrance: the evidence of the body at each
case with the invariant, with the invariant at each exit to the entrance. -/
def loop {a : K.At X} (Inv : K.At X → Type p) (body : Continuation S K (K :: Qs))
    (bodyDep : (a : K.At X) → Inv a → body.RunDep r (Exits.At.elim Inv P) a) (start : Inv a) :
    (Continuation.loop body).RunDep r P a :=
  fun limit n _ done => unrolled limit n Inv bodyDep done n a start

end Continuation.RunDep

/-- The lift of a diagram for a specification: the evidence at each context with a witness of
the precondition, for the postcondition of that witness. -/
abbrev Diagram.Lift (r : DepPoly.{0, 0, w, z} (S.interface X)) {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, w', p} (Diagram.interface X Γ Qs)) (d : Diagram S Γ Qs) :
    Type (max w z w' (p + 1)) :=
  (env : All X Γ) → (pre : q.Pre env) → d.RunDep r (q.Post env pre) env

/-- The lift of a continuation for a specification. -/
abbrev Continuation.Lift (r : DepPoly.{0, 0, w, z} (S.interface X)) {K : Boundary Ty}
    {Qs : Exits Ty} (t : DepPoly.{0, 0, w', p} (Continuation.interface X K Qs))
    (k : Continuation S K Qs) : Type (max w z w' (p + 1)) :=
  (a : K.At X) → (pre : t.Pre a) → k.RunDep r (t.Post a pre) a

/-- A verified diagram: the implementation with its lift, for a computation at the limit that
has evidence of each postcondition. -/
def Diagram.Lift.impl {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', p} (Diagram.interface X Γ Qs)} {d : Diagram S Γ Qs}
    (lift : d.Lift r q) {stop : Free (S.interface X) (Qs.At X)}
    (limit : (env : All X Γ) → (pre : q.Pre env) → FreeDep r (q.Post env pre) stop) (n : Nat) :
    ImplDep q r (d.impl stop n) :=
  fun env pre => lift env pre (limit env pre) n fun _ post => .pure post

/-- A verified continuation: the implementation with its lift. -/
def Continuation.Lift.impl {K : Boundary Ty} {Qs : Exits Ty}
    {t : DepPoly.{0, 0, w', p} (Continuation.interface X K Qs)} {k : Continuation S K Qs}
    (lift : k.Lift r t) {stop : Free (S.interface X) (Qs.At X)}
    (limit : (a : K.At X) → (pre : t.Pre a) → FreeDep r (t.Post a pre) stop) (n : Nat) :
    ImplDep t r (k.impl stop n) :=
  fun a pre => lift a pre (limit a pre) n fun _ post => .pure post

/-- A derivation in a rule set that holds after the substitution of a lowering gives a map of
verified implementations of one specification. The agreement that the derivation gives is its
plain part, and the lift moves along it. -/
def Diagram.Derivation.lift {D : Container.{0, 0}} {lower : Impl (S.interface X) D}
    {R : Rules S} {Γ : List Ty} {Qs : Exits Ty}
    (ok : R.Sound (Free.Congruence.subst (α := Qs.At X) lower))
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation R d e)
    {q : DepPoly.{0, 0, w', p} (Diagram.interface X Γ Qs)} {t : DepPoly.{0, 0, w, z} D}
    (stop : Free (S.interface X) (Qs.At X)) (n : Nat)
    (ff : ImplDep q t ((d.impl stop n).trans lower)) :
    ImplDep q t ((e.impl stop n).trans lower) :=
  ImplDep.reindex (fun env => Diagram.Derivation.sound stop n ok h env .pure) ff

end Draft
