import Prelude

/-! Diagrams over a signature.

A diagram goes from a context to its exits. A context is a list of value types, and a port is
a position of that list. A boundary is a list of contexts, and a case is a position of that
list. The exits are a list of boundaries, and a whole diagram has one boundary. A diagram is
an exit, a step, or a composite. A composite has a first diagram and a continuation. The
boundary of the continuation is the first boundary of the exits of the first diagram, and the
other boundaries are the exits of the composite. An exit names its boundary by a position of
the list, so an exit to the nearest continuation has a constructor of its own. A continuation
goes from its boundary to its exits. It is a copairing, with one diagram for each case, a
frame, with one diagram for all the cases and a bypass that keeps a case and its ports, or a
loop, with a body whose exits to the boundary are the next entrances. Two exits to one case are
a join.

A step is an operation with a port for each operand: an element of the extension of the
signature polynomial at the ports of the context. A diagram has two meanings, and each is a
recursion on the diagram. The function meaning goes into `Free` on the request interface of the
signature, with the remaining computation as an argument. Each loop has a given number of
unrollings, and a given computation at the limit. The run family goes into Type-valued
relations, for a relation of calls with a runtime, and the runs of a loop are the inductive
family of the runs of its body. The static size of a diagram is the number of its steps.

A port map acts on the context of a diagram, and a map of exits acts on its exits. A
family with a diagram for each exit case gives the diagram with those diagrams at its exits.
The derivations of a rule set are the smallest relation on diagrams that has the rules and
structural agreement, and that is an equivalence and a congruence for each form. An
implementation in which each rule holds gives computations that agree for each derivation, for
each number of unrollings. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v w

open Prelude Container

namespace Draft

variable {Ty : Type}

/-- A sum of control cases, with a product of typed ports in each case: the list of the
contexts of the cases. -/
abbrev Boundary (Ty : Type) : Type := List (List Ty)

namespace Boundary

/-- A case of a boundary: a position of its list, with the context at that position. -/
def Case (Q : Boundary Ty) : Type := (Δ : List Ty) × Elem Δ Q

/-- A case with an `X` at each of its ports: the extension of the boundary at `X`. -/
def At (Q : Boundary Ty) (X : Ty → Type) : Type :=
  (c : Q.Case) × All X c.1

/-- The boundary with one case. -/
def one (Γ : List Ty) : Boundary Ty := [Γ]

/-- The case of the boundary with one case. -/
def only (Γ : List Ty) : (one Γ).Case := ⟨Γ, .here⟩

/-- The sum of a number for each case. -/
def sum : (Q : Boundary Ty) → (Q.Case → Nat) → Nat
  | [], _ => 0
  | Δ :: Q, f => f ⟨Δ, .here⟩ + sum Q (fun c => f ⟨c.1, .there c.2⟩)

/-- The product of two boundaries: a case for each pair of their cases, with the ports of the
two cases. -/
def product : Boundary Ty → Boundary Ty → Boundary Ty
  | [], _ => []
  | Ξ :: M, K => K.map (· ++ Ξ) ++ product M K

/-- The position of a pair of cases in the product. -/
def pairElem {K : Boundary Ty} {Ξ Δ : List Ty} {M : Boundary Ty} (j : Elem Ξ M)
    (k : Elem Δ K) : Elem (Δ ++ Ξ) (product M K) :=
  Elem.casesOn (motive := fun M _ => Elem (Δ ++ Ξ) (product M K)) j (k.map (· ++ Ξ)).left
    (fun i => Elem.right _ (pairElem i k))

/-- The case of the product for a pair of cases. -/
def pair {M K : Boundary Ty} (j : M.Case) (c : K.Case) : (product M K).Case :=
  ⟨c.1 ++ j.1, pairElem j.2 c.2⟩

/-- The value at a case, from a table with one value for each case of the boundary. -/
def family {F : List Ty → Type} {Q : Boundary Ty} (table : All F Q) (c : Q.Case) : F c.1 :=
  table.lookup c.2

end Boundary

/-- A pure operation is central. An effectful operation has the runtime wire. -/
inductive Kind where
  | pure
  | effectful

/-- Operations with a product of typed input ports and an output boundary. A test is an
operation whose output boundary has two or more cases. -/
structure Signature (Ty : Type) where
  Op : Type
  kind : Op → Kind
  input : Op → List Ty
  output : Op → Boundary Ty

/-- The request interface of a signature at a family `X`. A request is an operation with an
`X` at each input port, and a response is an output case with an `X` at each of its ports. -/
def Signature.interface (S : Signature Ty) (X : Ty → Type) : Container where
  Shape := (o : S.Op) × All X (S.input o)
  Pos a := (S.output a.1).At X

/-- Each pure operation returns without a call in an implementation of the request
interface. -/
def Signature.Returns (S : Signature Ty) {X : Ty → Type} {D : Container.{u, v}}
    (impl : Impl (S.interface X) D) : Type (max u v) :=
  (o : S.Op) → S.kind o ≡ .pure → (args : All X (S.input o)) → impl.Returns ⟨o, args⟩

/-- A port of a context. -/
abbrev Port (Γ : List Ty) (t : Ty) : Type := Elem t Γ

/-- A port of `Γ` for each port of `Δ`. It copies, discards, and exchanges ports. -/
abbrev PortMap (Γ Δ : List Ty) : Type := All (Port Γ) Δ

namespace PortMap

/-- The port map into a context with more ports. -/
def weaken (Ξ : List Ty) {Γ Δ : List Ty} (ports : PortMap Γ Δ) : PortMap (Ξ ++ Γ) Δ :=
  ports.map (fun _ i => i.right Ξ)

/-- The exchange of the first two parts of a context. -/
def exchange (Ξ Θ Γ : List Ty) : PortMap (Ξ ++ (Θ ++ Γ)) (Θ ++ (Ξ ++ Γ)) :=
  (All.tabulate Θ (fun _ i => i.left.right Ξ)).append
    ((All.tabulate Ξ (fun _ i => i.left)).append
      (All.tabulate Γ (fun _ i => (i.right Θ).right Ξ)))

variable {X : Ty → Type}

/-- The selection at weakened ports has the values of the context only. -/
def selectWeaken {Ξ Γ Δ : List Ty} (extra : All X Ξ) (env : All X Γ) (ports : PortMap Γ Δ) :
    (extra.append env).select (ports.weaken Ξ) ≡ env.select ports :=
  (All.mapMap _ _ ports).trans (All.mapCongr (fun _ i => All.lookupRight extra env i) ports)

/-- The selection at the exchange has the first two parts in the other order. -/
def selectExchange {Ξ Θ Γ : List Ty} (x : All X Ξ) (y : All X Θ) (env : All X Γ) :
    (x.append (y.append env)).select (exchange Ξ Θ Γ) ≡ y.append (x.append env) :=
  (All.selectAppend _ _ _).trans
    (Identity.cong₂ All.append
      (All.selectTabulate _ y _ fun _ i =>
        (All.lookupRight x _ i.left).trans (All.lookupLeft y env i))
      ((All.selectAppend _ _ _).trans
        (Identity.cong₂ All.append
          (All.selectTabulate _ x _ fun _ i => All.lookupLeft x _ i)
          (All.selectTabulate _ env _ fun _ i =>
            (All.lookupRight x _ (i.right Θ)).trans (All.lookupRight y env i)))))

/-- The identity port map. -/
def id (Γ : List Ty) : PortMap Γ Γ := All.tabulate Γ (fun _ i => i)

/-- The selection at the identity port map has the values. -/
def selectId {Γ : List Ty} (env : All X Γ) : env.select (id Γ) ≡ env :=
  All.selectTabulate env env _ fun _ _ => .refl

/-- The port map under more ports: each added port is itself, and each other port is the port
that the map gives. -/
def lift (Ξ : List Ty) {Γ Δ : List Ty} (ports : PortMap Γ Δ) : PortMap (Ξ ++ Γ) (Ξ ++ Δ) :=
  (All.tabulate Ξ (fun _ i => i.left)).append (ports.weaken Ξ)

/-- The selection at a lifted port map has the added values and the selected values. -/
def selectLift {Ξ Γ Δ : List Ty} (extra : All X Ξ) (env : All X Γ) (ports : PortMap Γ Δ) :
    (extra.append env).select (ports.lift Ξ) ≡ extra.append (env.select ports) :=
  (All.selectAppend _ _ _).trans
    (Identity.cong₂ All.append
      (All.selectTabulate _ extra _ fun _ i => All.lookupLeft extra env i)
      (selectWeaken extra env ports))

end PortMap

/-- The exits of a diagram: a list of boundaries. The first boundary is the boundary of the
nearest continuation, and each other boundary is an exit around that continuation. -/
abbrev Exits (Ty : Type) : Type := List (Boundary Ty)

namespace Exits

/-- An exit with an `X` at each of its ports: a boundary of the exits, and a case of that
boundary with its values. -/
def At (Qs : Exits Ty) (X : Ty → Type) : Type := (Q : Boundary Ty) × Elem Q Qs × Q.At X

/-- A map of exits: a position in `Qs'` for each boundary of `Qs`. -/
abbrev Map (Qs Qs' : Exits Ty) : Type := (Q : Boundary Ty) → Elem Q Qs → Elem Q Qs'

/-- The map into the exits with one more first boundary. -/
def Map.there (K : Boundary Ty) (Qs : Exits Ty) : Map Qs (K :: Qs) := fun _ i => .there i

/-- The map under one more first boundary: that boundary is itself, and each other boundary
has the position that the map gives. -/
def Map.lift (K : Boundary Ty) {Qs Qs' : Exits Ty} (f : Map Qs Qs') :
    Map (K :: Qs) (K :: Qs') :=
  fun _ i => Elem.consCases (motive := fun Q _ => Elem Q (K :: Qs')) i .here
    (fun Q j => .there (f Q j))

namespace At

variable {K : Boundary Ty} {Qs Qs' : Exits Ty} {X : Ty → Type}

/-- The exit to a case of the first boundary. -/
def here (k : K.At X) : Exits.At (K :: Qs) X := ⟨K, .here, k⟩

/-- An exit under one more first boundary. -/
def there (K : Boundary Ty) (r : Qs.At X) : Exits.At (K :: Qs) X := ⟨r.1, .there r.2.1, r.2.2⟩

/-- The exit with the values of an environment at its ports. -/
def select {Γ : List Ty} (out : Qs.At (Port Γ)) (env : All X Γ) : Qs.At X :=
  ⟨out.1, out.2.1, out.2.2.1, env.select out.2.2.2⟩

/-- The exit at the position that a map gives to its boundary. -/
def map (f : Map Qs Qs') (r : Qs.At X) : Qs'.At X := ⟨r.1, f r.1 r.2.1, r.2.2⟩

/-- The value at an exit, from a function on the cases of the first boundary and a function
on the other exits. An exit to the first boundary has the position `.here`, so its value is
the value of the first function by computation, for each case. -/
def elim {β : Type w} (onHead : K.At X → β) (onTail : Qs.At X → β)
    (r : Exits.At (K :: Qs) X) : β :=
  Elem.consCases (motive := fun Q _ => Q.At X → β) r.2.1 onHead (fun Q j q => onTail ⟨Q, j, q⟩)
    r.2.2

/-- A value of each type from an exit of the empty list of boundaries. -/
def ofNil {β : Type w} (r : Exits.At ([] : Exits Ty) X) : β := r.2.1.ofNil

/-- The value at an exit of one boundary. -/
def only {β : Type w} (onHead : K.At X → β) : Exits.At [K] X → β := elim onHead ofNil

variable {β : Type u} {β' : Type v} {R : β → β' → Type w} {onHead : K.At X → β}
  {onTail : Qs.At X → β} {onHead' : K.At X → β'} {onTail' : Qs.At X → β'}

/-- A relation between the two functions of the first boundary, and between the two functions
of the other exits, holds at each exit. -/
def elimRel (head : (k : K.At X) → R (onHead k) (onHead' k))
    (tail : (q : Qs.At X) → R (onTail q) (onTail' q)) (r : Exits.At (K :: Qs) X) :
    R (elim onHead onTail r) (elim onHead' onTail' r) :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) →
      R (elim onHead onTail ⟨Q, i, q⟩) (elim onHead' onTail' ⟨Q, i, q⟩))
    r.2.1 head (fun Q j q => tail ⟨Q, j, q⟩) r.2.2

/-- A relation between two functions of the one boundary holds at each exit. -/
def onlyRel (head : (k : K.At X) → R (onHead k) (onHead' k)) (r : Exits.At [K] X) :
    R (only onHead r) (only onHead' r) :=
  elimRel head (fun q => q.ofNil) r

end At

end Exits

mutual

/-- A diagram from a context to its exits. -/
inductive Diagram (S : Signature Ty) : List Ty → Exits Ty → Type where
  /-- An exit: a case of a boundary of the exits, with a port of the context for each port
  of that case. -/
  | exit {Γ : List Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ)) : Diagram S Γ Qs
  /-- An operation with a port of the context for each operand, and one diagram for each
  output case. That diagram has the output ports of the case and the ports of the context. -/
  | step {Γ : List Ty} {Qs : Exits Ty} (call : (S.interface (Port Γ)).Shape)
      (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs) : Diagram S Γ Qs
  /-- A first diagram and a continuation. The boundary of the continuation is the first
  boundary of the exits of the first diagram, and the other boundaries are the exits of the
  composite. -/
  | seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
      (next : Continuation S K Qs) : Diagram S Γ Qs

/-- A continuation from a boundary to its exits. -/
inductive Continuation (S : Signature Ty) : Boundary Ty → Exits Ty → Type where
  /-- One diagram for each case. That diagram has the ports of the case only. -/
  | copair {K : Boundary Ty} {Qs : Exits Ty} (each : (c : K.Case) → Diagram S c.1 Qs) :
      Continuation S K Qs
  /-- One diagram for all the cases, whiskered by a bypass. Each case gives a case of the
  bypass with its ports, and it gives the ports of the diagram. The diagram has one boundary,
  and the continuation goes from the product of the bypass and that boundary. -/
  | frame {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      (kept : (c : P.Case) → M.At (Port c.1))
      (args : (c : P.Case) → PortMap c.1 Δ) (shared : Diagram S Δ [K])
      (next : Continuation S (M.product K) Qs) : Continuation S P Qs
  /-- The loop of a body. The first boundary of the exits of the body is the boundary of the
  loop, and an exit of the body to that boundary is the next entrance. Each other exit of the
  body is an exit of the loop. -/
  | loop {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs)) :
      Continuation S K Qs

end

variable {S : Signature Ty} {X : Ty → Type} {α : Type}

/-- The computation of a loop with a number of unrollings, from the computation of its body.
With no unrolling it is `stop`. With one more unrolling it is the body, with the loop at each
exit to the entrance and the remaining computation at each other exit. -/
def Continuation.unrolled {K : Boundary Ty} {Qs : Exits Ty} {β : Type w} (stop : β)
    (body : K.At X → (Exits.At (K :: Qs) X → β) → β) : Nat → K.At X → (Qs.At X → β) → β
  | 0, _, _ => stop
  | m + 1, k, rest => body k (Exits.At.elim (fun k' => unrolled stop body m k' rest) rest)

/-- A loop with one more unrolling is its body, with the loop at each exit to the entrance.
The identity holds by computation. -/
def Continuation.unrolledSucc {K : Boundary Ty} {Qs : Exits Ty} {β : Type w} (stop : β)
    (body : K.At X → (Exits.At (K :: Qs) X → β) → β) (m : Nat) (k : K.At X)
    (rest : Qs.At X → β) :
    Continuation.unrolled stop body (m + 1) k rest ≡
      body k (Exits.At.elim (fun k' => Continuation.unrolled stop body m k' rest) rest) :=
  .refl

/-- A relation between two loops with one number of unrollings, from the relation between
their bodies: the two bodies are related when the two loops are related at each exit to the
entrance. -/
def Continuation.unrolledRel {K : Boundary Ty} {Qs Qs' : Exits Ty} {β : Type u} {β' : Type v}
    {R : β → β' → Type w} {stop : β} {stop' : β'} (limit : R stop stop')
    {body : K.At X → (Exits.At (K :: Qs) X → β) → β}
    {body' : K.At X → (Exits.At (K :: Qs') X → β') → β'}
    {rest : Qs.At X → β} {rest' : Qs'.At X → β'}
    (step : (k : K.At X) → {again : K.At X → β} → {again' : K.At X → β'} →
      ((k' : K.At X) → R (again k') (again' k')) →
      R (body k (Exits.At.elim again rest)) (body' k (Exits.At.elim again' rest'))) :
    (m : Nat) → (k : K.At X) →
      R (unrolled stop body m k rest) (unrolled stop' body' m k rest')
  | 0, _ => limit
  | m + 1, k => step k (fun k' => unrolledRel limit step m k')

mutual

/-- The function meaning of a diagram: the computation at the values of its context, with the
remaining computation at each exit. Each loop has `n` unrollings, and `stop` is the computation
of a loop at the limit. A step is a request, and its continuation has one case for each
response. The first diagram of a composite has the computation of the continuation at an exit
to its boundary, and the remaining computation of the composite at each other exit. -/
def Diagram.run (stop : Free (S.interface X) α) (n : Nat) : {Γ : List Ty} → {Qs : Exits Ty} →
    Diagram S Γ Qs → All X Γ → (Qs.At X → Free (S.interface X) α) → Free (S.interface X) α
  | _, _, .exit out, env, rest => rest (out.select env)
  | _, _, .step call next, env, rest =>
      .request ⟨call.1, env.select call.2⟩ fun r => (next r.1).run stop n (r.2.append env) rest
  | _, _, .seq first next, env, rest =>
      first.run stop n env (Exits.At.elim (fun k => next.run stop n k rest) rest)

/-- The computation of a continuation at a case with its values. A frame gives the case of its
bypass, the kept values, and the exit of its diagram to its continuation. A loop has the
unrollings of its body. -/
def Continuation.run (stop : Free (S.interface X) α) (n : Nat) : {P : Boundary Ty} →
    {Qs : Exits Ty} → Continuation S P Qs → P.At X → (Qs.At X → Free (S.interface X) α) →
    Free (S.interface X) α
  | _, _, .copair each, r, rest => (each r.1).run stop n r.2 rest
  | _, _, .frame kept args shared next, r, rest =>
      shared.run stop n (r.2.select (args r.1)) (Exits.At.only fun out =>
        next.run stop n
          ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (r.2.select (kept r.1).2)⟩ rest)
  | _, _, .loop body, k, rest => Continuation.unrolled stop (body.run stop n) n k rest

end

/-- The computation that returns the exit case with its values. -/
def Diagram.meaning {Γ : List Ty} {Qs : Exits Ty} (stop : Free (S.interface X) (Qs.At X))
    (n : Nat) (d : Diagram S Γ Qs) (env : All X Γ) : Free (S.interface X) (Qs.At X) :=
  d.run stop n env .pure

variable (stop : Free (S.interface X) α) (n : Nat)

mutual

/-- The static size of a diagram: the number of its steps. A family has the sum of the sizes
of its cases. -/
def Diagram.size : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Nat
  | _, _, .exit _ => 0
  | _, _, .step call rest => 1 + (S.output call.1).sum fun c => (rest c).size
  | _, _, .seq first next => first.size + next.size

/-- The static size of a continuation. A frame has one count of its diagram, and a loop has
one count of its body. -/
def Continuation.size : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs → Nat
  | P, _, .copair each => P.sum fun c => (each c).size
  | _, _, .frame _ _ shared next => shared.size + next.size
  | _, _, .loop body => body.size

end

/-- The family of a step whose operation has one output case. -/
def Diagram.one {Δ Γ : List Ty} {Qs : Exits Ty} (d : Diagram S (Δ ++ Γ) Qs) :
    (c : (Boundary.one Δ).Case) → Diagram S (c.1 ++ Γ) Qs :=
  Boundary.family (F := fun Δ => Diagram S (Δ ++ Γ) Qs) (.cons d .nil)

/-- The copairing over the boundary with one case. -/
def Continuation.one {Δ : List Ty} {Qs : Exits Ty} (d : Diagram S Δ Qs) :
    Continuation S (.one Δ) Qs :=
  .copair (Boundary.family (F := fun Δ => Diagram S Δ Qs) (.cons d .nil))

mutual

/-- The computation of a diagram respects agreement of the remaining computations. -/
def Diagram.runCongr : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (env : All X Γ) → {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement (rest r) (rest' r)) →
    Free.Agreement (d.run stop n env rest) (d.run stop n env rest')
  | _, _, .exit _, _, _, _, same => same _
  | _, _, .step _ next, env, _, _, same =>
      .request _ fun r => (next r.1).runCongr (r.2.append env) same
  | _, _, .seq first next, env, _, _, same =>
      first.runCongr env
        (Exits.At.elimRel (R := Free.Agreement) (fun k => next.runCongr k same) same)

def Continuation.runCongr : {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) →
    (r : P.At X) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement (rest r) (rest' r)) →
    Free.Agreement (k.run stop n r rest) (k.run stop n r rest')
  | _, _, .copair each, r, _, _, same => (each r.1).runCongr r.2 same
  | _, _, .frame _ _ shared next, _, _, _, same =>
      shared.runCongr _ (Exits.At.onlyRel (R := Free.Agreement) fun _ => next.runCongr _ same)
  | _, _, .loop body, k, _, _, same =>
      Continuation.unrolledRel (R := Free.Agreement) (.refl stop)
        (fun k {_ _} again =>
          body.runCongr k (Exits.At.elimRel (R := Free.Agreement) again same)) n k

end

mutual

/-- Structural agreement of two diagrams: the same form with the same ports, and agreement of
the diagrams of each case. Two families that agree at each case can be different functions,
so this relation, and not identity, relates two forms of one diagram. -/
inductive Diagram.Agreement : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Diagram S Γ Qs → Type where
  | exit {Γ : List Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ)) :
      Diagram.Agreement (.exit out) (.exit out)
  | step {Γ : List Ty} {Qs : Exits Ty} (call : (S.interface (Port Γ)).Shape)
      {rest rest' : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs}
      (each : (c : (S.output call.1).Case) → Diagram.Agreement (rest c) (rest' c)) :
      Diagram.Agreement (.step call rest) (.step call rest')
  | seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} {first first' : Diagram S Γ (K :: Qs)}
      {next next' : Continuation S K Qs} (head : Diagram.Agreement first first')
      (tail : Continuation.Agreement next next') :
      Diagram.Agreement (.seq first next) (.seq first' next')

/-- Structural agreement of two continuations. The entry of a frame agrees at each case. -/
inductive Continuation.Agreement : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs →
    Continuation S P Qs → Type where
  | copair {K : Boundary Ty} {Qs : Exits Ty} {each each' : (c : K.Case) → Diagram S c.1 Qs}
      (cases : (c : K.Case) → Diagram.Agreement (each c) (each' c)) :
      Continuation.Agreement (.copair each) (.copair each')
  | frame {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      {kept kept' : (c : P.Case) → M.At (Port c.1)}
      {args args' : (c : P.Case) → PortMap c.1 Δ} {shared shared' : Diagram S Δ [K]}
      {next next' : Continuation S (M.product K) Qs}
      (keptSame : (c : P.Case) → kept c ≡ kept' c)
      (argsSame : (c : P.Case) → args c ≡ args' c)
      (body : Diagram.Agreement shared shared') (tail : Continuation.Agreement next next') :
      Continuation.Agreement (.frame kept args shared next) (.frame kept' args' shared' next')
  | loop {K : Boundary Ty} {Qs : Exits Ty} {body body' : Continuation S K (K :: Qs)}
      (same : Continuation.Agreement body body') :
      Continuation.Agreement (.loop body) (.loop body')

end

mutual

def Diagram.Agreement.refl : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    Diagram.Agreement d d
  | _, _, .exit out => .exit out
  | _, _, .step call rest => .step call fun c => Diagram.Agreement.refl (rest c)
  | _, _, .seq first next =>
      .seq (Diagram.Agreement.refl first) (Continuation.Agreement.refl next)

def Continuation.Agreement.refl : {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) →
    Continuation.Agreement k k
  | _, _, .copair each => .copair fun c => Diagram.Agreement.refl (each c)
  | _, _, .frame _ _ shared next =>
      .frame (fun _ => .refl) (fun _ => .refl) (Diagram.Agreement.refl shared)
        (Continuation.Agreement.refl next)
  | _, _, .loop body => .loop (Continuation.Agreement.refl body)

end

mutual

/-- Two diagrams that agree have computations that agree. -/
def Diagram.Agreement.run : {Γ : List Ty} → {Qs : Exits Ty} → {d d' : Diagram S Γ Qs} →
    Diagram.Agreement d d' → (env : All X Γ) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement (rest r) (rest' r)) →
    Free.Agreement (d.run stop n env rest) (d'.run stop n env rest')
  | _, _, _, _, .exit _, _, _, _, same => same _
  | _, _, _, _, .step _ each, env, _, _, same =>
      .request _ fun r => (each r.1).run (r.2.append env) same
  | _, _, _, _, .seq head tail, env, _, _, same =>
      head.run env (Exits.At.elimRel (R := Free.Agreement) (fun k => tail.run k same) same)

def Continuation.Agreement.run : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} →
    Continuation.Agreement k k' → (r : P.At X) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement (rest r) (rest' r)) →
    Free.Agreement (k.run stop n r rest) (k'.run stop n r rest')
  | _, _, _, _, .copair cases, r, _, _, same => (cases r.1).run r.2 same
  | _, _, _, _, .frame (kept := kept) (kept' := kept') (args := args) (args' := args')
      (shared := shared) (shared' := shared') (next := next) (next' := next')
      keptSame argsSame body tail, r, rest, rest', same =>
      Identity.transport
        (fun a => Free.Agreement
          (shared.run stop n (r.2.select (args r.1)) (Exits.At.only fun out =>
            next.run stop n ⟨Boundary.pair (kept r.1).1 out.1,
              out.2.append (r.2.select (kept r.1).2)⟩ rest))
          (shared'.run stop n (r.2.select a) (Exits.At.only fun out =>
            next'.run stop n ⟨Boundary.pair (kept' r.1).1 out.1,
              out.2.append (r.2.select (kept' r.1).2)⟩ rest')))
        (argsSame r.1)
        (Identity.transport
          (fun k => Free.Agreement
            (shared.run stop n (r.2.select (args r.1)) (Exits.At.only fun out =>
              next.run stop n ⟨Boundary.pair (kept r.1).1 out.1,
                out.2.append (r.2.select (kept r.1).2)⟩ rest))
            (shared'.run stop n (r.2.select (args r.1)) (Exits.At.only fun out =>
              next'.run stop n ⟨Boundary.pair k.1 out.1,
                out.2.append (r.2.select k.2)⟩ rest')))
          (keptSame r.1)
          (body.run _ (Exits.At.onlyRel (R := Free.Agreement) fun _ => tail.run _ same)))
  | _, _, _, _, .loop tail, k, _, _, same =>
      Continuation.unrolledRel (R := Free.Agreement) (.refl stop)
        (fun k {_ _} again =>
          tail.run k (Exits.At.elimRel (R := Free.Agreement) again same)) n k

end

namespace Diagram

/-- An exit to the boundary of a continuation, and then the continuation, is the continuation
at the case of the exit, with the values that the port map of the exit selects. The identity
holds by computation for each case. -/
def exitSeq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : K.At (Port Γ))
    (next : Continuation S K Qs) (env : All X Γ) (rest : Qs.At X → Free (S.interface X) α) :
    (Diagram.seq (.exit (Exits.At.here out)) next).run stop n env rest ≡
      next.run stop n ⟨out.1, env.select out.2⟩ rest :=
  .refl

/-- An exit past a continuation, and then the continuation, is that exit. The identity holds
by computation for each exit. -/
def exitPast {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ))
    (next : Continuation S K Qs) (env : All X Γ) (rest : Qs.At X → Free (S.interface X) α) :
    (Diagram.seq (.exit (out.there K)) next).run stop n env rest ≡ rest (out.select env) :=
  .refl

end Diagram

/-- The computation of a loop is the computation of its body, with the number of unrollings.
The identity holds by computation. -/
def Continuation.loopRun {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
    (k : K.At X) (rest : Qs.At X → Free (S.interface X) α) :
    (Continuation.loop body).run stop n k rest ≡
      Continuation.unrolled stop (body.run stop n) n k rest :=
  .refl

/-- A relation of calls with a runtime: the runs of a request from a runtime to a response and
a runtime. -/
abbrev Signature.Calls (S : Signature Ty) (X : Ty → Type) (R : Type u) : Type (max u (v + 1)) :=
  (a : (S.interface X).Shape) → R → (S.interface X).Pos a → R → Type v

/-- The result of a run of a loop body: an exit of the loop with a runtime, or the next
entrance with a runtime. -/
def Exits.At.result {K : Boundary Ty} {Qs : Exits Ty} {R : Type u} (r : Exits.At (K :: Qs) X)
    (s : R) : (Qs.At X × R) ⊕ (K.At X × R) :=
  Exits.At.elim (fun k => .inr (k, s)) (fun q => .inl (q, s)) r

mutual

/-- The run family of a diagram, for a relation of calls: the runs from the values of the
context and a runtime to an exit and a runtime. An exit is the graph of its function. A run of
a step has a response with a runtime, a run of the call, and a run of the diagram of the
response. A composite is the composition of its first diagram and the relation that has the
runs of the continuation at an exit to its boundary, and the identity at each other exit. -/
def Diagram.Runs {R : Type u} (T : Signature.Calls.{u, v} S X R) : {Γ : List Ty} →
    {Qs : Exits Ty} → Diagram S Γ Qs → Rel.{u, u, max u v} (All X Γ × R) (Qs.At X × R)
  | _, _, .exit out => Rel.lift.{u, u, u, v} (Rel.graph fun a => (out.select a.1, a.2))
  | _, _, .step call next => fun a b =>
      (x : (S.output call.1).At X × R) ×
        (T ⟨call.1, a.1.select call.2⟩ a.2 x.1 x.2 ×
          (next x.1.1).Runs T (x.1.2.append a.1, x.2) b)
  | _, _, .seq first next =>
      Rel.seq (first.Runs T) fun m b =>
        Exits.At.elim (fun k => next.Runs T (k, m.2) b) (fun q => ULift.{v} ((q, m.2) ≡ b)) m.1

/-- The run family of a continuation, from a case with its values and a runtime. A run of a
frame has a run of its diagram to an exit, and a run of its continuation from the case of the
bypass, the kept values, and that exit. The runs of a loop are the loop of the body and then
the graph of the result. -/
def Continuation.Runs {R : Type u} (T : Signature.Calls.{u, v} S X R) : {P : Boundary Ty} →
    {Qs : Exits Ty} → Continuation S P Qs → Rel.{u, u, max u v} (P.At X × R) (Qs.At X × R)
  | _, _, .copair each => fun a b => (each a.1.1).Runs T (a.1.2, a.2) b
  | _, _, .frame (K := K) kept args shared next => fun a b =>
      (m : Exits.At [K] X × R) ×
        (shared.Runs T (a.1.2.select (args a.1.1), a.2) m ×
          Exits.At.only (fun out =>
            next.Runs T
              (⟨Boundary.pair (kept a.1.1).1 out.1,
                out.2.append (a.1.2.select (kept a.1.1).2)⟩, m.2) b) m.1)
  | _, Qs, .loop (K := K) body =>
      Loop (A := K.At X × R) (B := Qs.At X × R)
        (Rel.seq (body.Runs T) (Rel.graph fun m => m.1.result m.2))

end

/-- One iteration of a loop: the body, and then the graph of the result. -/
abbrev Continuation.Iteration {R : Type u} (T : Signature.Calls.{u, v} S X R) {K : Boundary Ty}
    {Qs : Exits Ty} (body : Continuation S K (K :: Qs)) :
    Rel.{u, u, max u v} (K.At X × R) ((Qs.At X × R) ⊕ (K.At X × R)) :=
  Rel.seq (body.Runs T) (Rel.graph fun m => m.1.result m.2)

section

variable {R : Type u} (T : Signature.Calls.{u, v} S X R)

/-- The first exit equation of the run family: an exit to the boundary of a continuation, and
then the continuation, has the runs of the continuation at the case of the exit. The
equivalence is the law of the graph of a function and then a computation. -/
def Diagram.exitSeqRuns {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : K.At (Port Γ))
    (next : Continuation S K Qs) (a : All X Γ × R) (b : Qs.At X × R) :
    Iso ((Diagram.seq (.exit (Exits.At.here out)) next).Runs T a b)
      (next.Runs T (⟨out.1, a.1.select out.2⟩, a.2) b) :=
  Rel.graphSeq (fun a : All X Γ × R => ((Exits.At.here out).select a.1, a.2))
    (fun m b =>
      Exits.At.elim (fun k => next.Runs T (k, m.2) b) (fun q => ULift.{v} ((q, m.2) ≡ b)) m.1)
    a b

/-- The second exit equation of the run family: an exit past a continuation, and then the
continuation, has the runs of that exit. -/
def Diagram.exitPastRuns {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ))
    (next : Continuation S K Qs) (a : All X Γ × R) (b : Qs.At X × R) :
    Iso ((Diagram.seq (.exit (out.there K)) next).Runs T a b)
      ((Diagram.exit (S := S) out).Runs T a b) :=
  Rel.graphSeq (fun a : All X Γ × R => ((out.there K).select a.1, a.2))
    (fun m b =>
      Exits.At.elim (fun k => next.Runs T (k, m.2) b) (fun q => ULift.{v} ((q, m.2) ≡ b)) m.1)
    a b

/-- The runs of a loop are the runs of the loop of its iterations. The identity holds by
computation. -/
def Continuation.loopRuns {K : Boundary Ty} {Qs : Exits Ty} (body : Continuation S K (K :: Qs))
    (a : K.At X × R) (b : Qs.At X × R) :
    (Continuation.loop body).Runs T a b ≡ Loop (body.Iteration T) a b :=
  .refl

end

/-- The action of a port map on a diagram. The result has the context of the map, and each
use of a port is the port that the map gives. A continuation has the ports of its cases only,
so the action stops at a composite. -/
def Diagram.rename : {Γ Δ : List Ty} → {Qs : Exits Ty} → PortMap Γ Δ → Diagram S Δ Qs →
    Diagram S Γ Qs
  | _, _, _, ρ, .exit out => .exit (out.select ρ)
  | _, _, _, ρ, .step call rest =>
      .step ⟨call.1, ρ.select call.2⟩ fun c => Diagram.rename (ρ.lift c.1) (rest c)
  | _, _, _, ρ, .seq first next => .seq (Diagram.rename ρ first) next

/-- The computation of a diagram with renamed ports is the computation of the diagram at the
selected values. -/
def Diagram.renameRun : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) →
    (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((Diagram.rename ρ d).run stop n env rest) (d.run stop n (env.select ρ) rest)
  | _, _, _, ρ, .exit out, env, rest =>
      .ofIdentity (Identity.cong (fun vals => rest ⟨out.1, out.2.1, out.2.2.1, vals⟩)
        (All.selectSelect env ρ out.2.2.2))
  | _, _, _, ρ, .step call next, env, rest =>
      Identity.transport
        (fun args => Free.Agreement
          (.request (C := S.interface X) ⟨call.1, env.select (ρ.select call.2)⟩ fun r =>
            (Diagram.rename (ρ.lift r.1.1) (next r.1)).run stop n (r.2.append env) rest)
          (.request (C := S.interface X) ⟨call.1, args⟩ fun r =>
            (next r.1).run stop n (r.2.append (env.select ρ)) rest))
        (All.selectSelect env ρ call.2)
        (.request _ fun r =>
          (Diagram.renameRun (ρ.lift r.1.1) (next r.1) (r.2.append env) rest).trans
            (.ofIdentity (Identity.cong (fun vals => (next r.1).run stop n vals rest)
              (PortMap.selectLift r.2 env ρ))))
  | _, _, _, ρ, .seq first next, env, rest =>
      Diagram.renameRun ρ first env (Exits.At.elim (fun k => next.run stop n k rest) rest)

/-- The diagram with the ports of the identity map has the computation of the diagram. -/
def Diagram.renameIdRun {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (env : All X Γ)
    (rest : Qs.At X → Free (S.interface X) α) :
    Free.Agreement ((d.rename (.id Γ)).run stop n env rest) (d.run stop n env rest) :=
  (Diagram.renameRun stop n (.id Γ) d env rest).trans
    (.ofIdentity (Identity.cong (fun values => d.run stop n values rest)
      (All.selectTabulate env env _ fun _ _ => .refl)))

/-- Two renamings and the renaming by the composite map have one computation. -/
def Diagram.renameRenameRun {Γ Δ Θ : List Ty} {Qs : Exits Ty} (first : PortMap Γ Δ)
    (second : PortMap Δ Θ) (d : Diagram S Θ Qs) (env : All X Γ)
    (rest : Qs.At X → Free (S.interface X) α) :
    Free.Agreement (((d.rename second).rename first).run stop n env rest)
      ((d.rename (first.select second)).run stop n env rest) :=
  ((Diagram.renameRun stop n first (d.rename second) env rest).trans
      (Diagram.renameRun stop n second d (env.select first) rest)).trans
    ((Free.Agreement.ofIdentity (Identity.cong (fun values => d.run stop n values rest)
        (All.selectSelect env first second).symm)).trans
      (Diagram.renameRun stop n (first.select second) d env rest).symm)

mutual

/-- The action of a map of exits on a diagram. Each exit has the position that the map gives
to its boundary. -/
def Diagram.mapExit : {Γ : List Ty} → {Qs Qs' : Exits Ty} → Exits.Map Qs Qs' →
    Diagram S Γ Qs → Diagram S Γ Qs'
  | _, _, _, f, .exit out => .exit (Exits.At.map f out)
  | _, _, _, f, .step call rest => .step call fun c => Diagram.mapExit f (rest c)
  | _, _, _, f, .seq (K := K) first next =>
      .seq (Diagram.mapExit (Exits.Map.lift K f) first) (Continuation.mapExit f next)

def Continuation.mapExit : {P : Boundary Ty} → {Qs Qs' : Exits Ty} → Exits.Map Qs Qs' →
    Continuation S P Qs → Continuation S P Qs'
  | _, _, _, f, .copair each => .copair fun c => Diagram.mapExit f (each c)
  | _, _, _, f, .frame kept args shared next =>
      .frame kept args shared (Continuation.mapExit f next)
  | _, _, _, f, .loop (K := K) body => .loop (Continuation.mapExit (Exits.Map.lift K f) body)

end

/-- The remaining computation of the first diagram of a composite, at the exit that a lifted
map gives. An exit to the continuation stays, and each other exit goes to the remaining
computation at the exit that the map gives. -/
def Exits.Map.liftElim {K : Boundary Ty} {Qs Qs' : Exits Ty} (f : Exits.Map Qs Qs')
    {onHead onHead' : K.At X → Free (S.interface X) α}
    (rest : Qs'.At X → Free (S.interface X) α)
    (head : (k : K.At X) → Free.Agreement (onHead k) (onHead' k)) (r : Exits.At (K :: Qs) X) :
    Free.Agreement (Exits.At.elim onHead rest (Exits.At.map (Exits.Map.lift K f) r))
      (Exits.At.elim onHead' (fun b => rest (Exits.At.map f b)) r) :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) →
      Free.Agreement
        (Exits.At.elim onHead rest (Exits.At.map (Exits.Map.lift K f) ⟨Q, i, q⟩))
        (Exits.At.elim onHead' (fun b => rest (Exits.At.map f b)) ⟨Q, i, q⟩))
    r.2.1 head (fun Q j q => .refl (rest ⟨Q, f Q j, q⟩)) r.2.2

mutual

/-- The computation of a diagram with mapped exits is the computation of the diagram, with the
remaining computation at the exit that the map gives. -/
def Diagram.mapExitRun : {Γ : List Ty} → {Qs Qs' : Exits Ty} → (f : Exits.Map Qs Qs') →
    (d : Diagram S Γ Qs) → (env : All X Γ) → (rest : Qs'.At X → Free (S.interface X) α) →
    Free.Agreement ((Diagram.mapExit f d).run stop n env rest)
      (d.run stop n env fun r => rest (Exits.At.map f r))
  | _, _, _, f, .exit out, env, rest => .refl (rest (Exits.At.map f (out.select env)))
  | _, _, _, f, .step _ next, env, rest =>
      .request _ fun r => Diagram.mapExitRun f (next r.1) (r.2.append env) rest
  | _, _, _, f, .seq (K := K) first next, env, rest =>
      (Diagram.mapExitRun (Exits.Map.lift K f) first env
          (Exits.At.elim (fun k => (Continuation.mapExit f next).run stop n k rest) rest)).trans
        (first.runCongr stop n env
          (Exits.Map.liftElim f rest fun k => Continuation.mapExitRun f next k rest))

def Continuation.mapExitRun : {P : Boundary Ty} → {Qs Qs' : Exits Ty} →
    (f : Exits.Map Qs Qs') → (k : Continuation S P Qs) → (r : P.At X) →
    (rest : Qs'.At X → Free (S.interface X) α) →
    Free.Agreement ((Continuation.mapExit f k).run stop n r rest)
      (k.run stop n r fun b => rest (Exits.At.map f b))
  | _, _, _, f, .copair each, r, rest => Diagram.mapExitRun f (each r.1) r.2 rest
  | _, _, _, f, .frame _ _ shared next, _, rest =>
      shared.runCongr stop n _
        (Exits.At.onlyRel (R := Free.Agreement) fun _ => Continuation.mapExitRun f next _ rest)
  | _, _, _, f, .loop (K := K) body, k, rest =>
      Continuation.unrolledRel (R := Free.Agreement) (.refl stop)
        (fun k {again _} loops =>
          (Continuation.mapExitRun (Exits.Map.lift K f) body k (Exits.At.elim again rest)).trans
            (body.runCongr stop n k (Exits.Map.liftElim f rest loops)))
        n k

end

/-- A diagram for each case of each boundary of the exits `Qs`, in the context of the case,
with the exits `Qs'`. -/
abbrev Diagram.Family (S : Signature Ty) (Qs Qs' : Exits Ty) : Type :=
  (Q : Boundary Ty) → Elem Q Qs → (c : Q.Case) → Diagram S c.1 Qs'

/-- The family under one more first boundary: a case of that boundary has the exit to it, and
each other case has its diagram with the exits under that boundary. -/
def Diagram.Family.lift (K : Boundary Ty) {Qs Qs' : Exits Ty} (σ : Diagram.Family S Qs Qs') :
    Diagram.Family S (K :: Qs) (K :: Qs') :=
  fun _ i => Elem.consCases (motive := fun Q _ => (c : Q.Case) → Diagram S c.1 (K :: Qs')) i
    (fun c => .exit (Exits.At.here ⟨c, PortMap.id c.1⟩))
    (fun Q j c => Diagram.mapExit (Exits.Map.there K Qs') (σ Q j c))

mutual

/-- The diagram with a diagram at each exit. The family has a diagram for each exit case, in
the context of the case, and the exit gives its ports to that diagram. -/
def Diagram.substExit : {Γ : List Ty} → {Qs Qs' : Exits Ty} → Diagram.Family S Qs Qs' →
    Diagram S Γ Qs → Diagram S Γ Qs'
  | _, _, _, σ, .exit out => Diagram.rename out.2.2.2 (σ out.1 out.2.1 out.2.2.1)
  | _, _, _, σ, .step call rest => .step call fun c => Diagram.substExit σ (rest c)
  | _, _, _, σ, .seq (K := K) first next =>
      .seq (Diagram.substExit (Diagram.Family.lift K σ) first) (Continuation.substExit σ next)

def Continuation.substExit : {P : Boundary Ty} → {Qs Qs' : Exits Ty} →
    Diagram.Family S Qs Qs' → Continuation S P Qs → Continuation S P Qs'
  | _, _, _, σ, .copair each => .copair fun c => Diagram.substExit σ (each c)
  | _, _, _, σ, .frame kept args shared next =>
      .frame kept args shared (Continuation.substExit σ next)
  | _, _, _, σ, .loop (K := K) body =>
      .loop (Continuation.substExit (Diagram.Family.lift K σ) body)

end

/-- The computation of the diagram that a lifted family gives to an exit, with the remaining
computation of the first diagram of a composite. -/
def Diagram.Family.liftRun {K : Boundary Ty} {Qs Qs' : Exits Ty} (σ : Diagram.Family S Qs Qs')
    {onHead onHead' : K.At X → Free (S.interface X) α}
    (rest : Qs'.At X → Free (S.interface X) α)
    (head : (k : K.At X) → Free.Agreement (onHead k) (onHead' k)) (r : Exits.At (K :: Qs) X) :
    Free.Agreement
      ((Diagram.Family.lift K σ r.1 r.2.1 r.2.2.1).run stop n r.2.2.2 (Exits.At.elim onHead rest))
      (Exits.At.elim onHead' (fun b => (σ b.1 b.2.1 b.2.2.1).run stop n b.2.2.2 rest) r) :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) →
      Free.Agreement
        ((Diagram.Family.lift K σ Q i q.1).run stop n q.2 (Exits.At.elim onHead rest))
        (Exits.At.elim onHead' (fun b => (σ b.1 b.2.1 b.2.2.1).run stop n b.2.2.2 rest) ⟨Q, i, q⟩))
    r.2.1
    (fun q =>
      (Free.Agreement.ofIdentity
        (Identity.cong (fun v => onHead ⟨q.1, v⟩) (PortMap.selectId q.2))).trans (head q))
    (fun Q j q =>
      (Diagram.mapExitRun stop n (Exits.Map.there K Qs') (σ Q j q.1) q.2
          (Exits.At.elim onHead rest)).trans
        ((σ Q j q.1).runCongr stop n q.2 fun b => .refl (rest b)))
    r.2.2

mutual

/-- The computation of a diagram with a diagram at each exit is the computation of the
diagram, with the computation of the diagram of the case at each exit. -/
def Diagram.substExitRun : {Γ : List Ty} → {Qs Qs' : Exits Ty} →
    (σ : Diagram.Family S Qs Qs') → (d : Diagram S Γ Qs) → (env : All X Γ) →
    (rest : Qs'.At X → Free (S.interface X) α) →
    Free.Agreement ((Diagram.substExit σ d).run stop n env rest)
      (d.run stop n env fun r => (σ r.1 r.2.1 r.2.2.1).run stop n r.2.2.2 rest)
  | _, _, _, σ, .exit out, env, rest =>
      Diagram.renameRun stop n out.2.2.2 (σ out.1 out.2.1 out.2.2.1) env rest
  | _, _, _, σ, .step _ next, env, rest =>
      .request _ fun r => Diagram.substExitRun σ (next r.1) (r.2.append env) rest
  | _, _, _, σ, .seq (K := K) first next, env, rest =>
      (Diagram.substExitRun (Diagram.Family.lift K σ) first env
          (Exits.At.elim (fun k => (Continuation.substExit σ next).run stop n k rest) rest)).trans
        (first.runCongr stop n env
          (Diagram.Family.liftRun stop n σ rest fun k => Continuation.substExitRun σ next k rest))

def Continuation.substExitRun : {P : Boundary Ty} → {Qs Qs' : Exits Ty} →
    (σ : Diagram.Family S Qs Qs') → (k : Continuation S P Qs) → (r : P.At X) →
    (rest : Qs'.At X → Free (S.interface X) α) →
    Free.Agreement ((Continuation.substExit σ k).run stop n r rest)
      (k.run stop n r fun b => (σ b.1 b.2.1 b.2.2.1).run stop n b.2.2.2 rest)
  | _, _, _, σ, .copair each, r, rest => Diagram.substExitRun σ (each r.1) r.2 rest
  | _, _, _, σ, .frame _ _ shared next, _, rest =>
      shared.runCongr stop n _
        (Exits.At.onlyRel (R := Free.Agreement) fun _ =>
          Continuation.substExitRun σ next _ rest)
  | _, _, _, σ, .loop (K := K) body, k, rest =>
      Continuation.unrolledRel (R := Free.Agreement) (.refl stop)
        (fun k {again _} loops =>
          (Continuation.substExitRun (Diagram.Family.lift K σ) body k
              (Exits.At.elim again rest)).trans
            (body.runCongr stop n k (Diagram.Family.liftRun stop n σ rest loops)))
        n k

end

/-- A case of a continuation, as a diagram in the context of the case: the exit to that case,
and then the continuation. -/
def Continuation.atCase {K : Boundary Ty} {Qs : Exits Ty} (next : Continuation S K Qs)
    (c : K.Case) : Diagram S c.1 Qs :=
  .seq (.exit (Exits.At.here ⟨c, PortMap.id c.1⟩)) next

/-- The family of a continuation for the exits of the first diagram of a composite. A case of
the boundary of the continuation has the exit to it and then the continuation, and each other
case has its exit. -/
def Continuation.exits {K : Boundary Ty} {Qs : Exits Ty} (next : Continuation S K Qs) :
    Diagram.Family S (K :: Qs) Qs :=
  fun _ i => Elem.consCases (motive := fun Q _ => (c : Q.Case) → Diagram S c.1 Qs) i
    next.atCase (fun Q j c => .exit ⟨Q, j, c, PortMap.id c.1⟩)

/-- The diagram with the continuation at each exit to its boundary. A composite is the shared
form of a continuation, and this diagram is the copied form. -/
def Diagram.atExits {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}
    (first : Diagram S Γ (K :: Qs)) (next : Continuation S K Qs) : Diagram S Γ Qs :=
  Diagram.substExit next.exits first

/-- The remaining computation of the first diagram of a composite is the computation of the
diagram that the family of the continuation gives to the exit. -/
def Continuation.exitsRun {K : Boundary Ty} {Qs : Exits Ty} (next : Continuation S K Qs)
    (rest : Qs.At X → Free (S.interface X) α) (r : Exits.At (K :: Qs) X) :
    Free.Agreement (Exits.At.elim (fun k => next.run stop n k rest) rest r)
      ((next.exits r.1 r.2.1 r.2.2.1).run stop n r.2.2.2 rest) :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q (K :: Qs)) => (q : Q.At X) →
      Free.Agreement (Exits.At.elim (fun k => next.run stop n k rest) rest ⟨Q, i, q⟩)
        ((next.exits Q i q.1).run stop n q.2 rest))
    r.2.1
    (fun q =>
      .ofIdentity
        (Identity.cong (fun v => next.run stop n ⟨q.1, v⟩ rest) (PortMap.selectId q.2).symm))
    (fun Q j q =>
      .ofIdentity (Identity.cong (fun v => rest ⟨Q, j, q.1, v⟩) (PortMap.selectId q.2).symm))
    r.2.2

/-- The shared form and the copied form of a continuation have one meaning:
`[f, g] ; h = [f ; h, g ; h]`. -/
def Diagram.seqAtExits {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty}
    (first : Diagram S Γ (K :: Qs)) (next : Continuation S K Qs) (env : All X Γ)
    (rest : Qs.At X → Free (S.interface X) α) :
    Free.Agreement ((Diagram.seq first next).run stop n env rest)
      ((first.atExits next).run stop n env rest) :=
  (first.runCongr stop n env (next.exitsRun stop n rest)).trans
    (Diagram.substExitRun stop n next.exits first env rest).symm

/-- A rule set: a relation on diagrams and a relation on continuations. -/
structure Rules (S : Signature Ty) where
  diagram : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Diagram S Γ Qs → Type
  continuation : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs →
    Continuation S P Qs → Type

mutual

/-- The derivations of a rule set: the smallest relation that has the rules and structural
agreement, and that is an equivalence and a congruence for each form. -/
inductive Diagram.Derivation (R : Rules S) : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Diagram S Γ Qs → Type where
  | agree {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs}
      (same : Diagram.Agreement d e) : Diagram.Derivation R d e
  | rule {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs} (r : R.diagram d e) :
      Diagram.Derivation R d e
  | symm {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs} (h : Diagram.Derivation R d e) :
      Diagram.Derivation R e d
  | trans {Γ : List Ty} {Qs : Exits Ty} {d e f : Diagram S Γ Qs} (h : Diagram.Derivation R d e)
      (k : Diagram.Derivation R e f) : Diagram.Derivation R d f
  | step {Γ : List Ty} {Qs : Exits Ty} (call : (S.interface (Port Γ)).Shape)
      {rest rest' : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs}
      (each : (c : (S.output call.1).Case) → Diagram.Derivation R (rest c) (rest' c)) :
      Diagram.Derivation R (.step call rest) (.step call rest')
  | seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} {first first' : Diagram S Γ (K :: Qs)}
      {next next' : Continuation S K Qs} (head : Diagram.Derivation R first first')
      (tail : Continuation.Derivation R next next') :
      Diagram.Derivation R (.seq first next) (.seq first' next')

inductive Continuation.Derivation (R : Rules S) : {P : Boundary Ty} → {Qs : Exits Ty} →
    Continuation S P Qs →
    Continuation S P Qs → Type where
  | agree {P : Boundary Ty} {Qs : Exits Ty} {k k' : Continuation S P Qs}
      (same : Continuation.Agreement k k') : Continuation.Derivation R k k'
  | rule {P : Boundary Ty} {Qs : Exits Ty} {k k' : Continuation S P Qs} (r : R.continuation k k') :
      Continuation.Derivation R k k'
  | symm {P : Boundary Ty} {Qs : Exits Ty} {k k' : Continuation S P Qs}
      (h : Continuation.Derivation R k k') :
      Continuation.Derivation R k' k
  | trans {P : Boundary Ty} {Qs : Exits Ty} {k k' k'' : Continuation S P Qs}
      (h : Continuation.Derivation R k k')
      (j : Continuation.Derivation R k' k'') : Continuation.Derivation R k k''
  | copair {K : Boundary Ty} {Qs : Exits Ty} {each each' : (c : K.Case) → Diagram S c.1 Qs}
      (cases : (c : K.Case) → Diagram.Derivation R (each c) (each' c)) :
      Continuation.Derivation R (.copair each) (.copair each')
  | frame {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      (kept : (c : P.Case) → M.At (Port c.1))
      (args : (c : P.Case) → PortMap c.1 Δ) {shared shared' : Diagram S Δ [K]}
      {next next' : Continuation S (M.product K) Qs} (body : Diagram.Derivation R shared shared')
      (tail : Continuation.Derivation R next next') :
      Continuation.Derivation R (.frame kept args shared next) (.frame kept args shared' next')
  | loop {K : Boundary Ty} {Qs : Exits Ty} {body body' : Continuation S K (K :: Qs)}
      (same : Continuation.Derivation R body body') :
      Continuation.Derivation R (.loop body) (.loop body')

end

variable {D : Container.{u, v}} {impl : Impl (S.interface X) D}

mutual

/-- The computation of a diagram after the substitution respects agreement of the remaining
computations after the substitution. -/
def Diagram.runSubstCongr : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (env : All X Γ) → {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement ((rest r).subst impl) ((rest' r).subst impl)) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((d.run stop n env rest').subst impl)
  | _, _, .exit _, _, _, _, same => same _
  | _, _, .step call next, env, _, _, same =>
      Free.Agreement.bind (.refl (impl ⟨call.1, env.select call.2⟩)) fun r =>
        Diagram.runSubstCongr (next r.1) (r.2.append env) same
  | _, _, .seq first next, env, _, _, same =>
      Diagram.runSubstCongr first env
        (Exits.At.elimRel
          (R := fun (a b : Free (S.interface X) α) =>
            Free.Agreement (a.subst impl) (b.subst impl))
          (fun k => Continuation.runSubstCongr next k same) same)

def Continuation.runSubstCongr : {P : Boundary Ty} → {Qs : Exits Ty} →
    (k : Continuation S P Qs) → (r : P.At X) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → Free.Agreement ((rest r).subst impl) ((rest' r).subst impl)) →
    Free.Agreement ((k.run stop n r rest).subst impl) ((k.run stop n r rest').subst impl)
  | _, _, .copair each, r, _, _, same => Diagram.runSubstCongr (each r.1) r.2 same
  | _, _, .frame _ _ shared next, _, _, _, same =>
      Diagram.runSubstCongr shared _
        (Exits.At.onlyRel
          (R := fun (a b : Free (S.interface X) α) =>
            Free.Agreement (a.subst impl) (b.subst impl))
          fun _ => Continuation.runSubstCongr next _ same)
  | _, _, .loop body, k, _, _, same =>
      Continuation.unrolledRel
        (R := fun (a b : Free (S.interface X) α) =>
          Free.Agreement (a.subst impl) (b.subst impl))
        (Free.Agreement.refl (stop.subst impl))
        (fun k {_ _} again =>
          Continuation.runSubstCongr body k
            (Exits.At.elimRel
              (R := fun (a b : Free (S.interface X) α) =>
                Free.Agreement (a.subst impl) (b.subst impl))
              again same))
        n k

end

/-- Each rule of the set holds in the implementation, for each number of unrollings and each
computation at the limit. -/
structure Rules.Sound (R : Rules S) (impl : Impl (S.interface X) D) (α : Type) where
  diagram : (stop : Free (S.interface X) α) → (n : Nat) → {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → R.diagram d e →
    (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  continuation : (stop : Free (S.interface X) α) → (n : Nat) → {P : Boundary Ty} →
    {Qs : Exits Ty} → {k k' : Continuation S P Qs} → R.continuation k k' →
    (r : P.At X) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((k.run stop n r rest).subst impl) ((k'.run stop n r rest).subst impl)

variable {R : Rules S}

mutual

/-- An implementation in which each rule holds gives computations that agree for each
derivation. -/
def Diagram.Derivation.sound (ok : R.Sound impl α) : {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → Diagram.Derivation R d e → (env : All X Γ) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, _, _, .agree a, env, rest =>
      (a.run stop n env fun r => .refl (rest r)).subst (Impl.Agreement.refl impl)
  | _, _, _, _, .rule r, env, rest => ok.diagram stop n r env rest
  | _, _, _, _, .symm h, env, rest => (Diagram.Derivation.sound ok h env rest).symm
  | _, _, _, _, .trans h k, env, rest =>
      (Diagram.Derivation.sound ok h env rest).trans (Diagram.Derivation.sound ok k env rest)
  | _, _, _, _, .step call each, env, rest =>
      Free.Agreement.bind (.refl (impl ⟨call.1, env.select call.2⟩)) fun r =>
        Diagram.Derivation.sound ok (each r.1) (r.2.append env) rest
  | _, _, _, _, .seq (first' := first') (next := next) head tail, env, rest =>
      (Diagram.Derivation.sound ok head env
          (Exits.At.elim (fun k => next.run stop n k rest) rest)).trans
        (Diagram.runSubstCongr stop n first' env
          (Exits.At.elimRel
            (R := fun (a b : Free (S.interface X) α) =>
              Free.Agreement (a.subst impl) (b.subst impl))
            (fun k => Continuation.Derivation.sound ok tail k rest)
            (fun q => .refl ((rest q).subst impl))))

def Continuation.Derivation.sound (ok : R.Sound impl α) : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} → Continuation.Derivation R k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((k.run stop n r rest).subst impl) ((k'.run stop n r rest).subst impl)
  | _, _, _, _, .agree a, r, rest =>
      (a.run stop n r fun q => .refl (rest q)).subst (Impl.Agreement.refl impl)
  | _, _, _, _, .rule j, r, rest => ok.continuation stop n j r rest
  | _, _, _, _, .symm h, r, rest => (Continuation.Derivation.sound ok h r rest).symm
  | _, _, _, _, .trans h j, r, rest =>
      (Continuation.Derivation.sound ok h r rest).trans
        (Continuation.Derivation.sound ok j r rest)
  | _, _, _, _, .copair cases, r, rest => Diagram.Derivation.sound ok (cases r.1) r.2 rest
  | _, _, _, _, .frame (shared' := shared') (next := next) kept args body tail, r, rest =>
      (Diagram.Derivation.sound ok body (r.2.select (args r.1))
          (Exits.At.only fun out =>
            next.run stop n ⟨Boundary.pair (kept r.1).1 out.1,
              out.2.append (r.2.select (kept r.1).2)⟩ rest)).trans
        (Diagram.runSubstCongr stop n shared' (r.2.select (args r.1))
          (Exits.At.onlyRel
            (R := fun (a b : Free (S.interface X) α) =>
              Free.Agreement (a.subst impl) (b.subst impl))
            fun out =>
              Continuation.Derivation.sound ok tail
                ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (r.2.select (kept r.1).2)⟩
                rest))
  | _, _, _, _, .loop (body' := body') same, r, rest =>
      Continuation.unrolledRel
        (R := fun (a b : Free (S.interface X) α) =>
          Free.Agreement (a.subst impl) (b.subst impl))
        (Free.Agreement.refl (stop.subst impl))
        (fun k {again _} loops =>
          (Continuation.Derivation.sound ok same k (Exits.At.elim again rest)).trans
            (Continuation.runSubstCongr stop n body' k
              (Exits.At.elimRel
                (R := fun (a b : Free (S.interface X) α) =>
                  Free.Agreement (a.subst impl) (b.subst impl))
                loops (fun q => .refl ((rest q).subst impl)))))
        n r

end

/-- The interchange rule: two steps that no wire connects, of which one is pure, have two
orders. The rest of the second order has the two groups of output ports exchanged. -/
inductive Diagram.Interchange : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Diagram S Γ Qs →
    Type where
  | swap {Γ : List Ty} {Qs : Exits Ty} (a b : S.Op)
      (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
      (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
      (rest : (ca : (S.output a).Case) → (cb : (S.output b).Case) →
        Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs) :
      Diagram.Interchange
        (.step ⟨a, first⟩ fun ca => .step ⟨b, second.weaken _⟩ fun cb => rest ca cb)
        (.step ⟨b, second⟩ fun cb => .step ⟨a, first.weaken _⟩ fun ca =>
          Diagram.rename (PortMap.exchange _ _ Γ) (rest ca cb))

/-- The first exit equation of the control sum: an exit to the boundary of a copairing, and
then the copairing, is the diagram of the case of the exit, with renamed ports. -/
inductive Diagram.ExitCopair : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Diagram S Γ Qs → Type where
  | exit {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (c : K.Case) (ρ : PortMap Γ c.1)
      (each : (c : K.Case) → Diagram S c.1 Qs) :
      Diagram.ExitCopair (.seq (.exit (Exits.At.here ⟨c, ρ⟩)) (.copair each))
        (Diagram.rename ρ (each c))

/-- The second exit equation of the control sum: an exit past a continuation, and then the
continuation, is that exit. -/
inductive Diagram.ExitPast : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Diagram S Γ Qs → Type where
  | exit {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ))
      (next : Continuation S K Qs) :
      Diagram.ExitPast (.seq (.exit (out.there K)) next) (.exit out)

/-- The composite equation of the control sum: a composite is the diagram that has the
continuation at each exit to its boundary. The composite has one copy of the continuation. -/
inductive Diagram.SeqExits : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    Diagram S Γ Qs → Type where
  | seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Diagram S Γ (K :: Qs))
      (next : Continuation S K Qs) : Diagram.SeqExits (.seq first next) (first.atExits next)

/-- The frame of one case of the entry of a frame, as a diagram in the context of that case:
the exit to the boundary with that one case, and then the frame of that case. -/
def Continuation.frameAt {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (c : P.Case) :
    Diagram S c.1 Qs :=
  .seq (.exit (Exits.At.here ⟨Boundary.only c.1, PortMap.id c.1⟩))
    (.frame (Boundary.family (F := fun Γ => M.At (Port Γ)) (.cons (kept c) .nil))
      (Boundary.family (F := fun Γ => PortMap Γ Δ) (.cons (args c) .nil)) shared next)

/-- The frame equation of the control sum: a frame is the copairing that has the frame of each
case alone. The frame has one copy of its diagram, and the copairing has one copy for each
case. -/
inductive Continuation.FrameCopair : {P : Boundary Ty} → {Qs : Exits Ty} →
    Continuation S P Qs → Continuation S P Qs → Type where
  | frame {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
      (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) :
      Continuation.FrameCopair (.frame kept args shared next)
        (.copair (Continuation.frameAt kept args shared next))

/-- The case equation of the control sum: a continuation is the copairing of its cases. -/
inductive Continuation.CopairCases : {P : Boundary Ty} → {Qs : Exits Ty} →
    Continuation S P Qs → Continuation S P Qs → Type where
  | cases {K : Boundary Ty} {Qs : Exits Ty} (next : Continuation S K Qs) :
      Continuation.CopairCases next (.copair next.atCase)

/-- The interchange equation set. -/
def Rules.interchange (S : Signature Ty) : Rules S := ⟨Diagram.Interchange, fun _ _ => Empty⟩

/-- The interchange rule and the equations of the control sum: the two exit equations, the
composite equation, the frame equation, and the case equation. -/
def Rules.control (S : Signature Ty) : Rules S :=
  ⟨fun d e => Diagram.Interchange d e ⊕
      (Diagram.ExitCopair d e ⊕ (Diagram.ExitPast d e ⊕ Diagram.SeqExits d e)),
    fun k k' => Continuation.FrameCopair k k' ⊕ Continuation.CopairCases k k'⟩

/-- A map out of a sum is fixed by its cases: two continuations that have a derivation at each
case have a derivation. -/
def Continuation.Derivation.ofCases {K : Boundary Ty} {Qs : Exits Ty}
    {k k' : Continuation S K Qs}
    (each : (c : K.Case) → Diagram.Derivation (Rules.control S) (k.atCase c) (k'.atCase c)) :
    Continuation.Derivation (Rules.control S) k k' :=
  .trans (.rule (Sum.inr (.cases k)))
    (.trans (.copair each) (.symm (.rule (Sum.inr (.cases k')))))

/-- A call at weakened ports is the call at the ports. -/
def Diagram.callWeaken {β : Type} {Ξ Γ : List Ty} (o : S.Op) (ports : PortMap Γ (S.input o))
    (extra : All X Ξ) (env : All X Γ) (k : (S.output o).At X → Free D β) :
    Free.Agreement ((impl ⟨o, (extra.append env).select (ports.weaken _)⟩).bind k)
      ((impl ⟨o, env.select ports⟩).bind k) :=
  .ofIdentity (Identity.cong (fun args => (impl ⟨o, args⟩).bind k)
    (PortMap.selectWeaken extra env ports))

/-- The computation of a diagram with exchanged ports, at the values in the other order. -/
def Diagram.swapRest {Ξ Θ Γ : List Ty} {Qs : Exits Ty} (d : Diagram S (Θ ++ (Ξ ++ Γ)) Qs)
    (x : All X Ξ) (y : All X Θ) (env : All X Γ) (rest : Qs.At X → Free (S.interface X) α) :
    Free.Agreement
      (((Diagram.rename (PortMap.exchange Ξ Θ Γ) d).run stop n (x.append (y.append env)) rest).subst
        impl)
      ((d.run stop n (y.append (x.append env)) rest).subst impl) :=
  ((Diagram.renameRun stop n (PortMap.exchange Ξ Θ Γ) d _ rest).subst
      (Impl.Agreement.refl impl)).trans
    (.ofIdentity (Identity.cong (fun vals => (d.run stop n vals rest).subst impl)
      (PortMap.selectExchange x y env)))

/-- The interchange rule holds in each implementation in which each pure operation returns
without a call. The pure step gives its response to the rest in each order, and the two
contexts of the rest have the same values. -/
def Diagram.Interchange.sound (pure : S.Returns impl) {Γ : List Ty} {Qs : Exits Ty} :
    {d e : Diagram S Γ Qs} → Diagram.Interchange d e → (env : All X Γ) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, .swap a b (.inl central) first second after, env, rest =>
      let ra := pure a central (env.select first)
      ((ra.bind fun r =>
          (impl ⟨b, (r.2.append env).select (second.weaken _)⟩).bind fun rb =>
            ((after r.1 rb.1).run stop n (rb.2.append (r.2.append env)) rest).subst impl).trans
        (Diagram.callWeaken b second ra.response.2 env fun rb =>
          ((after ra.response.1 rb.1).run stop n (rb.2.append (ra.response.2.append env))
            rest).subst impl)).trans
        (Free.Agreement.bind (.refl (impl ⟨b, env.select second⟩)) fun rb =>
          (((Diagram.callWeaken a first rb.2 env fun r =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after r.1 rb.1)).run stop n
                (r.2.append (rb.2.append env)) rest).subst impl).trans
            (ra.bind fun r =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after r.1 rb.1)).run stop n
                (r.2.append (rb.2.append env)) rest).subst impl)).trans
            (Diagram.swapRest stop n (after ra.response.1 rb.1) ra.response.2 rb.2 env rest)).symm)
  | _, _, .swap a b (.inr central) first second after, env, rest =>
      let rb := pure b central (env.select second)
      (Free.Agreement.bind (.refl (impl ⟨a, env.select first⟩)) fun ra =>
          (Diagram.callWeaken b second ra.2 env fun r =>
            ((after ra.1 r.1).run stop n (r.2.append (ra.2.append env)) rest).subst impl).trans
          (rb.bind fun r =>
            ((after ra.1 r.1).run stop n (r.2.append (ra.2.append env)) rest).subst impl)).trans
        (((rb.bind fun r =>
            (impl ⟨a, (r.2.append env).select (first.weaken _)⟩).bind fun ra =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after ra.1 r.1)).run stop n
                (ra.2.append (r.2.append env)) rest).subst impl).trans
          ((Diagram.callWeaken a first rb.response.2 env fun ra =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after ra.1 rb.response.1)).run stop n
                (ra.2.append (rb.response.2.append env)) rest).subst impl).trans
            (Free.Agreement.bind (.refl (impl ⟨a, env.select first⟩)) fun ra =>
              Diagram.swapRest stop n (after ra.1 rb.response.1) ra.2 rb.response.2 env
                rest))).symm)

/-- The first exit equation of the control sum holds in each implementation. -/
def Diagram.ExitCopair.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.ExitCopair d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, .exit c ρ each, env, rest =>
      ((Diagram.renameRun stop n ρ (each c) env rest).subst (Impl.Agreement.refl impl)).symm

/-- The second exit equation of the control sum holds in each implementation. The two
computations are one computation. -/
def Diagram.ExitPast.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.ExitPast d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, .exit out _, env, rest => .refl ((rest (out.select env)).subst impl)

/-- The composite equation of the control sum holds in each implementation. -/
def Diagram.SeqExits.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.SeqExits d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, .seq first next, env, rest =>
      (Diagram.seqAtExits stop n first next env rest).subst (Impl.Agreement.refl impl)

/-- The frame equation of the control sum holds in each implementation. The frame of one case
has the values that the identity port map selects. -/
def Continuation.FrameCopair.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.FrameCopair k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((k.run stop n r rest).subst impl) ((k'.run stop n r rest).subst impl)
  | _, _, .frame kept args shared next, r, rest =>
      .ofIdentity
        (Identity.cong
          (fun (values : All X r.1.1) =>
            (shared.run stop n (values.select (args r.1)) (Exits.At.only fun out =>
              next.run stop n
                ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (values.select (kept r.1).2)⟩
                rest)).subst impl)
          (PortMap.selectId r.2).symm)

/-- The case equation of the control sum holds in each implementation. The case has the values
that the identity port map selects. -/
def Continuation.CopairCases.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.CopairCases k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((k.run stop n r rest).subst impl) ((k'.run stop n r rest).subst impl)
  | _, _, .cases next, r, rest =>
      .ofIdentity
        (Identity.cong
          (fun (values : All X r.1.1) => (next.run stop n ⟨r.1, values⟩ rest).subst impl)
          (PortMap.selectId r.2).symm)

/-- The interchange equation set holds in each implementation in which each pure operation
returns without a call. -/
def Rules.Sound.interchange (pure : S.Returns impl) : (Rules.interchange S).Sound impl α :=
  ⟨fun stop n => Diagram.Interchange.sound stop n pure, fun _ _ => fun r => nomatch r⟩

def Rules.Sound.control (pure : S.Returns impl) : (Rules.control S).Sound impl α :=
  ⟨fun stop n => fun r => match r with
    | .inl i => Diagram.Interchange.sound stop n pure i
    | .inr (.inl x) => Diagram.ExitCopair.sound stop n x
    | .inr (.inr (.inl x)) => Diagram.ExitPast.sound stop n x
    | .inr (.inr (.inr x)) => Diagram.SeqExits.sound stop n x,
    fun stop n => fun r => match r with
    | .inl x => Continuation.FrameCopair.sound stop n x
    | .inr x => Continuation.CopairCases.sound stop n x⟩

end Draft
