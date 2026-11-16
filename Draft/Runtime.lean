import Draft.Diagram

/-! Diagrams with a runtime.

A machine of the request interface of a signature has a runtime: for a call and a runtime it
gives a response with the next runtime, or it stops. The run of the function meaning of a
diagram on a machine has the runtime at each call in sequence. The relation of calls of a
machine is the graph of the machine at the calls that give a response.

A specification of the interface with a runtime relates the runtime before a call to the
response and the runtime after it. The evidence of a diagram for such a specification has the
same form as the function meaning with the runtime at each call. At the values of the context
and a runtime, for a condition at each exit with its runtime, a condition at a stop, and a
condition of the runtime at the limit of a loop: when the remaining computation has evidence at
each exit and each runtime with the condition, the computation of the diagram from the runtime
has evidence.

The evidence is built by the constructors of the diagram. A step has a witness of the
precondition of its call at the runtime, the condition at each stop, and the evidence of the
diagram of each response from the next runtime. The condition of a composite and the condition
of a frame have the runtime. The invariant of a loop has the runtime and the number of the
unrollings that remain: the body goes from the invariant at one more unrolling to the
invariant at the next entrance, and the invariant at no unrolling gives the condition at the
limit. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z p

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R : Type} {E : Type}

/-- The relation of calls of a machine: the graph of the machine at the calls that give a
response. -/
def Signature.callsOf (m : Machine (S.interface X) R E) : Signature.Calls.{0, 0} S X R :=
  fun a s i s' => m (a, s) ≡ .inr (i, s')

/-- The evidence of a diagram at the values of its context and a runtime, for a number of
unrollings: the dependent form of the function meaning with the runtime at each call. `P` is
the condition at each exit with its runtime, `Z` is the condition at a stop, and `L` is the
condition of the runtime at the limit of a loop. -/
abbrev Diagram.StateDep (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) (n : Nat)
    {Γ : List Ty} {Qs : Exits Ty} (P : Qs.At X → R → Type p) (Z : E → Type p) (L : R → Type p)
    (d : Diagram S Γ Qs) (env : All X Γ) (s : R) : Type (max w z (p + 1)) :=
  {α : Type} → {F : E ⊕ (α × R) → Type p} → {stop : Free (S.interface X) α} →
    ((e : E) → Z e → F (.inl e)) → ((s' : R) → L s' → FreeDep r F (stop.thread s')) →
    {cont : Qs.At X → Free (S.interface X) α} →
    ((x : Qs.At X) → (s' : R) → P x s' → FreeDep r F ((cont x).thread s')) →
    FreeDep r F ((d.run stop n env cont).thread s)

/-- The evidence of a continuation at a case with its values and a runtime. -/
abbrev Continuation.StateDep (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) (n : Nat)
    {K : Boundary Ty} {Qs : Exits Ty} (P : Qs.At X → R → Type p) (Z : E → Type p)
    (L : R → Type p) (k : Continuation S K Qs) (a : K.At X) (s : R) : Type (max w z (p + 1)) :=
  {α : Type} → {F : E ⊕ (α × R) → Type p} → {stop : Free (S.interface X) α} →
    ((e : E) → Z e → F (.inl e)) → ((s' : R) → L s' → FreeDep r F (stop.thread s')) →
    {cont : Qs.At X → Free (S.interface X) α} →
    ((x : Qs.At X) → (s' : R) → P x s' → FreeDep r F ((cont x).thread s')) →
    FreeDep r F ((k.run stop n a cont).thread s)

variable {r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)} {n : Nat}

namespace Diagram.StateDep

variable {Γ : List Ty} {Qs : Exits Ty} {P : Qs.At X → R → Type p} {Z : E → Type p}
  {L : R → Type p} {env : All X Γ} {s : R}

/-- The evidence of an exit: its condition at the runtime. -/
def exit (out : Qs.At (Port Γ)) (h : P (out.select env) s) :
    (Diagram.exit (S := S) out).StateDep r n P Z L env s :=
  fun _ _ _ done => done _ s h

/-- The evidence of a step: a witness of the precondition of the call at the runtime, the
condition at each stop, and the evidence of the diagram of each response from the next runtime,
which receives the postcondition. -/
def step (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    (admit : r.Pre (⟨call.1, env.select call.2⟩, s))
    (stopped : (e : E) → r.Post (⟨call.1, env.select call.2⟩, s) admit (.inl e) → Z e)
    (next : (resp : (S.output call.1).At X) → (s' : R) →
      r.Post (⟨call.1, env.select call.2⟩, s) admit (.inr (resp, s')) →
      (rest resp.1).StateDep r n P Z L (resp.2.append env) s') :
    (Diagram.step call rest).StateDep r n P Z L env s :=
  fun {_ F stop} stops limit cont done =>
    FreeDep.request (r := r) (shape := (⟨call.1, env.select call.2⟩, s))
      (next := Sum.elim (fun e => .pure (.inl e))
        (fun (b : (S.output call.1).At X × R) =>
          ((rest b.1.1).run stop n (b.1.2.append env) cont).thread b.2))
      admit
      fun b =>
        Sum.casesOn
          (motive := fun b => r.Post (⟨call.1, env.select call.2⟩, s) admit b →
            FreeDep r F
              (Sum.elim (fun e => Free.pure (.inl e))
                (fun (b : (S.output call.1).At X × R) =>
          ((rest b.1.1).run stop n (b.1.2.append env) cont).thread b.2) b))
          b (fun e post => .pure (stops e (stopped e post)))
          (fun b post => next b.1 b.2 post stops limit done)

/-- The evidence of a step for the graph of a machine, at a call where the machine gives a
response: the evidence of the diagram of that response from its next runtime. -/
def stepResponse (m : Machine (S.interface X) R E) (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs)
    {b : (S.output call.1).At X × R} (known : m (⟨call.1, env.select call.2⟩, s) ≡ .inr b)
    (next : (rest b.1.1).StateDep m.graph n P Z L (b.1.2.append env) b.2) :
    (Diagram.step call rest).StateDep m.graph n P Z L env s :=
  step (r := m.graph) (env := env) (s := s) call rest PUnit.unit
    (fun _ post => (Identity.inrNotInl (known.symm.trans post)).elim)
    (fun _ _ post =>
      Identity.transport
        (fun (c : (S.output call.1).At X × R) =>
          (rest c.1.1).StateDep m.graph n P Z L (c.1.2.append env) c.2)
        (Identity.inrInject (known.symm.trans post)) next)

/-- The evidence of a step for the graph of a machine, at a call where the machine stops: the
condition at that stop. -/
def stepStop (m : Machine (S.interface X) R E) (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs) {e : E}
    (known : m (⟨call.1, env.select call.2⟩, s) ≡ .inl e) (z : Z e) :
    (Diagram.step call rest).StateDep m.graph n P Z L env s :=
  step (r := m.graph) (env := env) (s := s) call rest PUnit.unit
    (fun _ post => Identity.transport Z (Identity.inlInject (known.symm.trans post)) z)
    (fun _ _ post => (Identity.inlNotInr (known.symm.trans post)).elim)

/-- The evidence of a composite, for a condition at the boundary of the continuation with its
runtime. -/
def seq {K : Boundary Ty} (Mid : K.At X → R → Type p) (first : Diagram S Γ (K :: Qs))
    (next : Continuation S K Qs) (firstDep : first.StateDep r n (Exits.At.elim Mid P) Z L env s)
    (nextDep : (a : K.At X) → (s' : R) → Mid a s' → next.StateDep r n P Z L a s') :
    (Diagram.seq first next).StateDep r n P Z L env s :=
  fun {α F _} stops limit _ done =>
    firstDep stops limit
      (Exits.At.elimRel
        (R := fun (A : R → Type p) (c : Free (S.interface X) α) =>
          (s' : R) → A s' → FreeDep r F (c.thread s'))
        (fun a s' mid => nextDep a s' mid stops limit done) (fun x s' post => done x s' post))

end Diagram.StateDep

namespace Continuation.StateDep

variable {K : Boundary Ty} {Qs : Exits Ty} {P : Qs.At X → R → Type p} {Z : E → Type p}
  {L : R → Type p} {s : R}

/-- The evidence of a copairing: the evidence of the diagram of the case. -/
def copair {a : K.At X} (each : (c : K.Case) → Diagram S c.1 Qs)
    (dep : (each a.1).StateDep r n P Z L a.2 s) :
    (Continuation.copair each).StateDep r n P Z L a s :=
  fun stops limit _ done => dep stops limit done

/-- The evidence of a frame, for a condition at the exit of its diagram with its runtime. -/
def frame {M B : Boundary Ty} {Δ : List Ty} {a : B.At X} (Mid : K.At X → R → Type p)
    (kept : (c : B.Case) → M.At (Port c.1)) (args : (c : B.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs)
    (sharedDep : shared.StateDep r n (Exits.At.only Mid) Z L (a.2.select (args a.1)) s)
    (nextDep : (out : K.At X) → (s' : R) → Mid out s' →
      next.StateDep r n P Z L
        ⟨Boundary.pair (kept a.1).1 out.1, out.2.append (a.2.select (kept a.1).2)⟩ s') :
    (Continuation.frame kept args shared next).StateDep r n P Z L a s :=
  fun {α F _} stops limit _ done =>
    sharedDep stops limit
      (Exits.At.onlyRel
        (R := fun (A : R → Type p) (c : Free (S.interface X) α) =>
          (s' : R) → A s' → FreeDep r F (c.thread s'))
        (fun out s' mid => nextDep out s' mid stops limit done))

/-- The evidence of a loop with a number of unrollings, for an invariant that has the number of
the unrollings that remain. With no unrolling it is the evidence at the limit. -/
def unrolled {α : Type} {F : E ⊕ (α × R) → Type p} {stop : Free (S.interface X) α}
    (stops : (e : E) → Z e → F (.inl e))
    (limit : (s' : R) → L s' → FreeDep r F (stop.thread s'))
    (Inv : Nat → K.At X → R → Type p) {body : Continuation S K (K :: Qs)}
    (bodyDep : (m : Nat) → (a : K.At X) → (s : R) → Inv (m + 1) a s →
      body.StateDep r n (Exits.At.elim (Inv m) P) Z L a s)
    (atLimit : (a : K.At X) → (s : R) → Inv 0 a s → L s)
    {cont : Qs.At X → Free (S.interface X) α}
    (done : (x : Qs.At X) → (s' : R) → P x s' → FreeDep r F ((cont x).thread s')) :
    (m : Nat) → (a : K.At X) → (s : R) → Inv m a s →
      FreeDep r F ((Continuation.unrolled stop (body.run stop n) m a cont).thread s)
  | 0, a, s, inv => limit s (atLimit a s inv)
  | m + 1, a, s, inv =>
      bodyDep m a s inv stops limit
        (Exits.At.elimRel
          (R := fun (A : R → Type p) (c : Free (S.interface X) α) =>
            (s' : R) → A s' → FreeDep r F (c.thread s'))
          (fun a' s' inv' => unrolled stops limit Inv bodyDep atLimit done m a' s' inv')
          (fun x s' post => done x s' post))

/-- The evidence of a loop, for an invariant that has the number of the unrollings that remain.
The body goes from the invariant at one more unrolling to the invariant at each exit to the
entrance. The invariant at no unrolling gives the condition at the limit. -/
def loop {a : K.At X} (Inv : Nat → K.At X → R → Type p) (body : Continuation S K (K :: Qs))
    (bodyDep : (m : Nat) → (a : K.At X) → (s : R) → Inv (m + 1) a s →
      body.StateDep r n (Exits.At.elim (Inv m) P) Z L a s)
    (atLimit : (a : K.At X) → (s : R) → Inv 0 a s → L s) (start : Inv n a s) :
    (Continuation.loop body).StateDep r n P Z L a s :=
  fun stops limit _ done => unrolled stops limit Inv bodyDep atLimit done n a s start

end Continuation.StateDep

end Draft
