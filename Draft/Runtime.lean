import Draft.Verified

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
limit.

A specification of a diagram with a runtime is a dependent polynomial on the interface of the
diagram with a runtime. The lift of a diagram for it has the evidence at each context and each
runtime with a witness of the precondition. The verified diagram is the implementation with a
runtime, with that lift. Its composition with a verified lowering with a runtime is a verified
implementation by the calls of the target with a runtime.

A derivation in a rule set that holds after the substitution of a lowering gives an agreement
of the two computations with a runtime, after the lowering with a runtime. A verified
implementation with a runtime moves along the agreement. Such a rule set holds on the machine
of the lowering, for each machine of the target.

A rule set can hold on a machine and not after a substitution: the two sides of a rule can have
different calls and one run. A derivation in such a rule set gives the identity of the machines
of its two diagrams at each call. The evidence of the machine of the first diagram moves along
that identity to the machine of the second diagram, for each specification of the interface of
the diagram with a runtime. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z p w' u v

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

/-- The lift of a diagram for a specification of its interface with a runtime: the evidence at
each context and each runtime with a witness of the precondition. The condition at an exit and
the condition at a stop are the postcondition of that witness. `L` is the condition of the
runtime at the limit of a loop. -/
abbrev Diagram.StateLift (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) (n : Nat)
    {Γ : List Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, w', p} ((Diagram.interface X Γ Qs).runtime R E))
    (L : (a : All X Γ × R) → q.Pre a → R → Type p) (d : Diagram S Γ Qs) :
    Type (max w z w' (p + 1)) :=
  (env : All X Γ) → (s : R) → (pre : q.Pre (env, s)) →
    d.StateDep r n (fun x s' => q.Post (env, s) pre (.inr (x, s')))
      (fun e => q.Post (env, s) pre (.inl e)) (L (env, s) pre) env s

/-- The lift of a continuation for a specification of its interface with a runtime. -/
abbrev Continuation.StateLift (r : DepPoly.{0, 0, w, z} ((S.interface X).runtime R E)) (n : Nat)
    {K : Boundary Ty} {Qs : Exits Ty}
    (q : DepPoly.{0, 0, w', p} ((Continuation.interface X K Qs).runtime R E))
    (L : (a : K.At X × R) → q.Pre a → R → Type p) (k : Continuation S K Qs) :
    Type (max w z w' (p + 1)) :=
  (a : K.At X) → (s : R) → (pre : q.Pre (a, s)) →
    k.StateDep r n (fun x s' => q.Post (a, s) pre (.inr (x, s')))
      (fun e => q.Post (a, s) pre (.inl e)) (L (a, s) pre) a s

/-- A verified diagram with a runtime: the implementation with a runtime, with its lift, for a
computation at the limit that has evidence of each postcondition. -/
def Diagram.StateLift.impl {Γ : List Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', p} ((Diagram.interface X Γ Qs).runtime R E)}
    {L : (a : All X Γ × R) → q.Pre a → R → Type p} {d : Diagram S Γ Qs}
    (lift : d.StateLift r n q L) {stop : Free (S.interface X) (Qs.At X)}
    (limit : (env : All X Γ) → (s : R) → (pre : q.Pre (env, s)) → (s' : R) →
      L (env, s) pre s' → FreeDep r (q.Post (env, s) pre) (stop.thread s')) :
    ImplDep q r (d.impl stop n).thread :=
  fun a pre => lift a.1 a.2 pre (fun _ z => z) (limit a.1 a.2 pre) fun _ _ post => .pure post

/-- A verified continuation with a runtime. -/
def Continuation.StateLift.impl {K : Boundary Ty} {Qs : Exits Ty}
    {q : DepPoly.{0, 0, w', p} ((Continuation.interface X K Qs).runtime R E)}
    {L : (a : K.At X × R) → q.Pre a → R → Type p} {k : Continuation S K Qs}
    (lift : k.StateLift r n q L) {stop : Free (S.interface X) (Qs.At X)}
    (limit : (a : K.At X) → (s : R) → (pre : q.Pre (a, s)) → (s' : R) →
      L (a, s) pre s' → FreeDep r (q.Post (a, s) pre) (stop.thread s')) :
    ImplDep q r (k.impl stop n).thread :=
  fun a pre => lift a.1 a.2 pre (fun _ z => z) (limit a.1 a.2 pre) fun _ _ post => .pure post

section Derivation

variable {D : Container.{u, v}} {lower : Impl (S.interface X) D} {T : Rules S} {α : Type}
  (stop : Free (S.interface X) α) (count : Nat)
  (ok : T.Sound (Free.Congruence.subst (α := α) lower))

/-- A derivation in a rule set that holds after the substitution of a lowering gives
computations with a runtime that agree, after the lowering with a runtime. -/
def Diagram.Derivation.thread {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs}
    (h : Diagram.Derivation T d e) (env : All X Γ) (rest : Qs.At X → Free (S.interface X) α)
    (s : R) :
    Free.Agreement (((d.run stop count env rest).thread (E := E) s).subst lower.thread)
      (((e.run stop count env rest).thread s).subst lower.thread) :=
  (Free.threadSubst lower (d.run stop count env rest) s).symm.trans
    ((Free.Agreement.thread (h.sound stop count ok env rest) s).trans
      (Free.threadSubst lower (e.run stop count env rest) s))

/-- The two continuations of a derivation, with a runtime. -/
def Continuation.Derivation.thread {K : Boundary Ty} {Qs : Exits Ty} {k k' : Continuation S K Qs}
    (h : Continuation.Derivation T k k') (a : K.At X) (rest : Qs.At X → Free (S.interface X) α)
    (s : R) :
    Free.Agreement (((k.run stop count a rest).thread (E := E) s).subst lower.thread)
      (((k'.run stop count a rest).thread s).subst lower.thread) :=
  (Free.threadSubst lower (k.run stop count a rest) s).symm.trans
    ((Free.Agreement.thread (h.sound stop count ok a rest) s).trans
      (Free.threadSubst lower (k'.run stop count a rest) s))

/-- Rules that hold after the substitution of a lowering hold on the machine of the lowering,
for each machine of the target. -/
def Rules.Sound.machine (m : Machine D R E) : T.Sound (α := α) (m.impl lower).congruence :=
  ok.map (Machine.runOfSubst lower m)

end Derivation

/-- A derivation in a rule set that holds after the substitution of a lowering gives a map of
verified implementations with a runtime, of one specification. The agreement of the two
computations with a runtime is its plain part, and the lift moves along it. -/
def Diagram.Derivation.stateLift {D : Container.{0, 0}} {lower : Impl (S.interface X) D}
    {T : Rules S} {Γ : List Ty} {Qs : Exits Ty}
    (ok : T.Sound (Free.Congruence.subst (α := Qs.At X) lower))
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation T d e)
    {q : DepPoly.{0, 0, w', p} ((Diagram.interface X Γ Qs).runtime R E)}
    {t : DepPoly.{0, 0, w, z} (D.runtime R E)} (stop : Free (S.interface X) (Qs.At X))
    (count : Nat) (ff : ImplDep q t ((d.impl stop count).thread.trans lower.thread)) :
    ImplDep q t ((e.impl stop count).thread.trans lower.thread) :=
  ImplDep.reindex (fun a => h.thread stop count ok a.1 .pure a.2) ff

section Machine

variable {m : Machine (S.interface X) R E} {T : Rules S} {Γ : List Ty} {Qs : Exits Ty}
  (ok : T.Sound (α := Qs.At X) m.congruence) {d e : Diagram S Γ Qs}
  (h : Diagram.Derivation T d e) (stop : Free (S.interface X) (Qs.At X)) (count : Nat)

/-- The two diagrams of a derivation have one machine, on each machine on which the rules
hold. -/
def Diagram.Derivation.machine :
    Homotopy (m.impl (d.impl stop count)) (m.impl (e.impl stop count)) :=
  fun a => h.sound stop count ok a.1 .pure a.2

/-- A derivation in a rule set that holds on a machine gives a map of the evidence of the
machine of a diagram, for one specification. The identity of the two machines at each call is
its plain part, and the evidence moves along it. -/
def Diagram.Derivation.evidence
    {q : DepPoly.{0, 0, w, z} ((Diagram.interface X Γ Qs).runtime R E)}
    (ev : Evidence q (m.impl (d.impl stop count))) : Evidence q (m.impl (e.impl stop count)) :=
  Evidence.reindex (h.machine ok stop count) ev

end Machine

end Draft
