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
structural agreement, and that is an equivalence and a congruence for each form. A congruence
of computations in which each rule holds relates the two computations of each derivation, for
each number of unrollings. Agreement after the substitution of an implementation is such a
congruence, and so is the identity of the runs on a machine.

A frame has two equations. A frame of a step is the step, and then the frame of the diagram of
each response. A frame of an exit is its continuation at the pair of the kept case and the case
of the exit. They give one theorem for each rule set that has the control equations: a
derivation between two diagrams with one boundary gives a derivation between the two diagrams
in a context, each with the rest in line at each exit. An equation between two closed sequences
of steps thus applies in each context and with each rest, by one application of the theorem. -/

set_option autoImplicit false
set_option genInjectivity false

universe u v w w' z'

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

/-- One of two kinds is the pure kind, or the two kinds are effectful. -/
def Kind.central : (k l : Kind) → Option ((k ≡ .pure) ⊕ (l ≡ .pure))
  | .pure, .pure => some (.inl .refl)
  | .pure, .effectful => some (.inl .refl)
  | .effectful, .pure => some (.inr .refl)
  | .effectful, .effectful => none

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

/-- The specification of the pure operations of the request interface: a witness of the
precondition of a call is the identity of the kind of its operation with the pure kind. An
implementation in which each pure operation returns without a call is a verified implementation
of this specification, for the specification that admits no call. -/
def Signature.pureSpec (S : Signature Ty) (X : Ty → Type) :
    DepPoly.{0, 0, 0, 0} (S.interface X) where
  Pre a := S.kind a.1 ≡ .pure
  Post _ _ _ := PUnit

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

/-- A port map into a context with more ports is a weakened port map when it has none of those
ports. -/
def strengthen (Ξ : List Ty) {Γ : List Ty} : {Δ : List Ty} → (ports : PortMap (Ξ ++ Γ) Δ) →
    Option ((inner : PortMap Γ Δ) × (ports ≡ inner.weaken Ξ))
  | _, .nil => some ⟨.nil, .refl⟩
  | _, .cons p ps =>
      match Elem.split Ξ p with
      | .inl _ => none
      | .inr found =>
          match strengthen Ξ ps with
          | none => none
          | some inner =>
              some ⟨.cons found.1 inner.1,
                Identity.cong₂ (fun q qs => All.cons q qs) found.2 inner.2⟩

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

/-- The selection of a port map at the identity port map has the ports. -/
def idSelect {Γ Δ : List Ty} (ports : PortMap Γ Δ) : (id Γ).select ports ≡ ports :=
  (All.mapCongr (fun _ i => All.lookupTabulate (fun _ j => j) i) ports).trans (All.mapId ports)

/-- The identity port map under more ports is the identity port map. -/
def liftId (Ξ Γ : List Ty) : (id Γ).lift Ξ ≡ id (Ξ ++ Γ) :=
  (Identity.cong
      (All.append (All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left)))
      (All.mapTabulate (fun (t : Ty) (i : Port Γ t) => (i.right Ξ : Port (Ξ ++ Γ) t)) Γ
        (fun _ i => i))).trans
    (All.tabulateAppend (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i)).symm

/-- The selection at a weakened port map is the weakened selection. -/
def weakenSelect (Ξ : List Ty) {Γ Δ Θ : List Ty} (first : PortMap Γ Δ) (second : PortMap Δ Θ) :
    (first.weaken Ξ).select second ≡ weaken Ξ (first.select second) :=
  (All.mapCongr
      (fun _ i =>
        All.lookupMap (fun (t : Ty) (j : Port Γ t) => (j.right Ξ : Port (Ξ ++ Γ) t)) first i)
      second).trans
    (All.mapMap _ _ second).symm

/-- The composite of two port maps under more ports is the composite under more ports. -/
def liftSelect (Ξ : List Ty) {Γ Δ Θ : List Ty} (first : PortMap Γ Δ) (second : PortMap Δ Θ) :
    (first.lift Ξ).select (second.lift Ξ) ≡ lift Ξ (first.select second) :=
  (selectLift (All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left)) (first.weaken Ξ)
      second).trans
    (Identity.cong (All.append (All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left)))
      (weakenSelect Ξ first second))

/-- The port map into the context with no more port is the port map. -/
def weakenNil {Γ Δ : List Ty} (ports : PortMap Γ Δ) : ports.weaken [] ≡ ports :=
  All.mapId ports

/-- The selection at ports that are transported along an identity of lists is the transported
selection. -/
def selectTransport {Γ Δ Δ' : List Ty} (e : Δ ≡ Δ') (ports : PortMap Γ Δ) (env : All X Γ) :
    env.select (Identity.transport (PortMap Γ) e ports) ≡
      Identity.transport (All X) e (env.select ports) :=
  (Identity.transportMap (fun (Θ : List Ty) (ps : PortMap Γ Θ) => env.select ps) e ports).symm

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

/-- The family of a step whose output boundary is identical to the boundary with one case. -/
def Diagram.oneAt {Δ Γ : List Ty} {Qs : Exits Ty} {K : Boundary Ty} (e : Boundary.one Δ ≡ K)
    (d : Diagram S (Δ ++ Γ) Qs) : (c : K.Case) → Diagram S (c.1 ++ Γ) Qs :=
  Identity.transport (fun K => (c : Boundary.Case K) → Diagram S (c.1 ++ Γ) Qs) e (Diagram.one d)

/-- The exit to the one case of one boundary, with its ports. -/
def Diagram.exitOne {Γ Δ : List Ty} (ports : PortMap Γ Δ) : Diagram S Γ [.one Δ] :=
  .exit ⟨_, .here, Boundary.only Δ, ports⟩

/-- The values of a response at the boundary with one case. -/
def Boundary.onlyValues {Δ : List Ty} (r : (Boundary.one Δ).At X) : All X Δ :=
  Elem.consCases (motive := fun (Ξ : List Ty) _ => All X Ξ → All X Δ) r.1.2 (fun v => v)
    (fun _ j => j.ofNil) r.2

/-- The values of a response, at a boundary that is identical to the boundary with one case. -/
def Boundary.valuesAt {Δ : List Ty} {K : Boundary Ty} (e : Boundary.one Δ ≡ K) :
    K.At X → All X Δ :=
  Identity.transport (fun K => Boundary.At K X → All X Δ) e Boundary.onlyValues

/-- The computation of the diagram of a response is the computation of the diagram of the one
case, at the values of the response. -/
def Diagram.oneAtRun {Δ Γ : List Ty} {Qs : Exits Ty} {K : Boundary Ty}
    (e : Boundary.one Δ ≡ K) (d : Diagram S (Δ ++ Γ) Qs) (env : All X Γ)
    (rest : Qs.At X → Free (S.interface X) α) (r : K.At X) :
    ((Diagram.oneAt e d) r.1).run stop n (r.2.append env) rest ≡
      d.run stop n ((Boundary.valuesAt e r).append env) rest :=
  Identity.ind
    (fun K e => (r : Boundary.At K X) →
      ((Diagram.oneAt e d) r.1).run stop n (r.2.append env) rest ≡
        d.run stop n ((Boundary.valuesAt e r).append env) rest)
    (fun r =>
      Elem.consCases
        (motive := fun (Δ' : List Ty) (i : Elem Δ' [Δ]) => (vals : All X Δ') →
          ((Diagram.one d) ⟨Δ', i⟩).run stop n (vals.append env) rest ≡
            d.run stop n ((Boundary.onlyValues (X := X) ⟨⟨Δ', i⟩, vals⟩).append env) rest)
        r.1.2 (fun _ => .refl) (fun _ j => j.ofNil) r.2)
    e r

/-- The copairing over the boundary with one case. -/
def Continuation.one {Δ : List Ty} {Qs : Exits Ty} (d : Diagram S Δ Qs) :
    Continuation S (.one Δ) Qs :=
  .copair (Boundary.family (F := fun Δ => Diagram S Δ Qs) (.cons d .nil))

mutual

/-- The computation of a diagram respects a congruence of the remaining computations. -/
def Diagram.runRel (eqv : Free.Congruence.{0, 0, 0, w} (S.interface X) α) : {Γ : List Ty} →
    {Qs : Exits Ty} → (d : Diagram S Γ Qs) → (env : All X Γ) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → eqv.Rel (rest r) (rest' r)) →
    eqv.Rel (d.run stop n env rest) (d.run stop n env rest')
  | _, _, .exit _, _, _, _, same => same _
  | _, _, .step _ next, env, _, _, same =>
      eqv.request _ fun r => Diagram.runRel eqv (next r.1) (r.2.append env) same
  | _, _, .seq first next, env, _, _, same =>
      Diagram.runRel eqv first env
        (Exits.At.elimRel (R := eqv.Rel) (fun k => Continuation.runRel eqv next k same) same)

def Continuation.runRel (eqv : Free.Congruence.{0, 0, 0, w} (S.interface X) α) :
    {P : Boundary Ty} → {Qs : Exits Ty} → (k : Continuation S P Qs) → (r : P.At X) →
    {rest rest' : Qs.At X → Free (S.interface X) α} →
    ((r : Qs.At X) → eqv.Rel (rest r) (rest' r)) →
    eqv.Rel (k.run stop n r rest) (k.run stop n r rest')
  | _, _, .copair each, r, _, _, same => Diagram.runRel eqv (each r.1) r.2 same
  | _, _, .frame _ _ shared next, _, _, _, same =>
      Diagram.runRel eqv shared _
        (Exits.At.onlyRel (R := eqv.Rel) fun _ => Continuation.runRel eqv next _ same)
  | _, _, .loop body, k, _, _, same =>
      Continuation.unrolledRel (R := eqv.Rel) (eqv.refl stop)
        (fun k {_ _} again =>
          Continuation.runRel eqv body k (Exits.At.elimRel (R := eqv.Rel) again same)) n k

end

/-- The computation of a diagram respects agreement of the remaining computations. -/
def Diagram.runCongr {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (env : All X Γ)
    {rest rest' : Qs.At X → Free (S.interface X) α}
    (same : (r : Qs.At X) → Free.Agreement (rest r) (rest' r)) :
    Free.Agreement (d.run stop n env rest) (d.run stop n env rest') :=
  d.runRel stop n (.agreement _ _) env same

def Continuation.runCongr {P : Boundary Ty} {Qs : Exits Ty} (k : Continuation S P Qs)
    (r : P.At X) {rest rest' : Qs.At X → Free (S.interface X) α}
    (same : (r : Qs.At X) → Free.Agreement (rest r) (rest' r)) :
    Free.Agreement (k.run stop n r rest) (k.run stop n r rest') :=
  k.runRel stop n (.agreement _ _) r same

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

/-- Two exits with identical ports agree. -/
def Diagram.Agreement.exitPorts {Γ : List Ty} {Qs : Exits Ty} (Q : Boundary Ty) (i : Elem Q Qs)
    (c : Q.Case) {ports ports' : PortMap Γ c.1} (same : ports ≡ ports') :
    Diagram.Agreement (S := S) (.exit ⟨Q, i, c, ports⟩) (.exit ⟨Q, i, c, ports'⟩) :=
  Identity.ind
    (fun ports' _ => Diagram.Agreement (S := S) (.exit ⟨Q, i, c, ports⟩) (.exit ⟨Q, i, c, ports'⟩))
    (.exit ⟨Q, i, c, ports⟩) same

/-- Two steps of one operation with identical ports agree when the diagrams of each case
agree. -/
def Diagram.Agreement.stepPorts {Γ : List Ty} {Qs : Exits Ty} (o : S.Op)
    {ports ports' : PortMap Γ (S.input o)} (same : ports ≡ ports')
    {rest rest' : (c : (S.output o).Case) → Diagram S (c.1 ++ Γ) Qs}
    (each : (c : (S.output o).Case) → Diagram.Agreement (rest c) (rest' c)) :
    Diagram.Agreement (.step ⟨o, ports⟩ rest) (.step ⟨o, ports'⟩ rest') :=
  Identity.ind
    (fun ports' _ => Diagram.Agreement (.step ⟨o, ports⟩ rest) (.step ⟨o, ports'⟩ rest'))
    (.step ⟨o, ports⟩ each) same

/-- Two renamings of one diagram by identical port maps agree. -/
def Diagram.Agreement.renamePorts {Γ Δ : List Ty} {Qs : Exits Ty} (d : Diagram S Δ Qs)
    {ρ ρ' : PortMap Γ Δ} (same : ρ ≡ ρ') : Diagram.Agreement (d.rename ρ) (d.rename ρ') :=
  Identity.ind (fun ρ' _ => Diagram.Agreement (d.rename ρ) (d.rename ρ'))
    (Diagram.Agreement.refl _) same

/-- A function of diagrams for each list of added ports, at the family of a step whose output
boundary is identical to the boundary with one case: an agreement at the one case gives the
agreement at each case. -/
def Diagram.oneAtAgree {Δ Γ Γ' : List Ty} {Qs Qs' : Exits Ty} {K : Boundary Ty}
    (e : Boundary.one Δ ≡ K)
    (F : (Ξ : List Ty) → Diagram S (Ξ ++ Γ) Qs → Diagram S (Ξ ++ Γ') Qs')
    {x : Diagram S (Δ ++ Γ) Qs} {y : Diagram S (Δ ++ Γ') Qs'}
    (same : Diagram.Agreement (F Δ x) y) (c : K.Case) :
    Diagram.Agreement (F c.1 (Diagram.oneAt e x c)) (Diagram.oneAt e y c) :=
  Identity.ind
    (fun K e => (c : Boundary.Case K) →
      Diagram.Agreement (F c.1 (Diagram.oneAt e x c)) (Diagram.oneAt e y c))
    (fun c =>
      Elem.consCases
        (motive := fun (Δ' : List Ty) (i : Elem Δ' [Δ]) =>
          Diagram.Agreement (F Δ' (Diagram.one x ⟨Δ', i⟩)) (Diagram.one y ⟨Δ', i⟩))
        c.2 same (fun _ i => i.ofNil))
    e c

/-- A diagram with the ports of a map that is the identity map agrees with the diagram. -/
def Diagram.renameAgree : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (ρ : PortMap Γ Γ) → ρ ≡ PortMap.id Γ → Diagram.Agreement (d.rename ρ) d
  | _, _, .exit out, _, same =>
      .exitPorts out.1 out.2.1 out.2.2.1
        ((Identity.cong (fun σ => All.select σ out.2.2.2) same).trans
          (PortMap.idSelect out.2.2.2))
  | _, _, .step call rest, ρ, same =>
      .stepPorts call.1
        ((Identity.cong (fun σ => All.select σ call.2) same).trans (PortMap.idSelect call.2))
        fun c =>
          Diagram.renameAgree (rest c) (ρ.lift c.1)
            ((Identity.cong (PortMap.lift c.1) same).trans (PortMap.liftId c.1 _))
  | _, _, .seq first next, ρ, same =>
      .seq (Diagram.renameAgree first ρ same) (Continuation.Agreement.refl next)

/-- The identity law of the action of a port map: the diagram with the ports of the identity
map agrees with the diagram. -/
def Diagram.renameId {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) :
    Diagram.Agreement (d.rename (.id Γ)) d :=
  d.renameAgree (.id Γ) .refl

/-- Two renamings agree with the renaming by a map that is the composite map. -/
def Diagram.renameCompose : {Γ Δ Θ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Θ Qs) →
    (first : PortMap Γ Δ) → (second : PortMap Δ Θ) → (ρ : PortMap Γ Θ) →
    first.select second ≡ ρ → Diagram.Agreement ((d.rename second).rename first) (d.rename ρ)
  | _, _, _, _, .exit out, first, second, _, same =>
      .exitPorts out.1 out.2.1 out.2.2.1
        ((All.selectSelect first second out.2.2.2).trans
          (Identity.cong (fun σ => All.select σ out.2.2.2) same))
  | _, _, _, _, .step call rest, first, second, ρ, same =>
      .stepPorts call.1
        ((All.selectSelect first second call.2).trans
          (Identity.cong (fun σ => All.select σ call.2) same))
        fun c =>
          Diagram.renameCompose (rest c) (first.lift c.1) (second.lift c.1) (ρ.lift c.1)
            ((PortMap.liftSelect c.1 first second).trans
              (Identity.cong (PortMap.lift c.1) same))
  | _, _, _, _, .seq d next, first, second, ρ, same =>
      .seq (Diagram.renameCompose d first second ρ same) (Continuation.Agreement.refl next)

/-- The composition law of the action of a port map: two renamings agree with the renaming by
the composite map. -/
def Diagram.renameRename {Γ Δ Θ : List Ty} {Qs : Exits Ty} (first : PortMap Γ Δ)
    (second : PortMap Δ Θ) (d : Diagram S Θ Qs) :
    Diagram.Agreement ((d.rename second).rename first) (d.rename (first.select second)) :=
  d.renameCompose first second _ .refl

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
  {eqv : Free.Congruence.{0, 0, 0, w} (S.interface X) α}

/-- Each rule of the set holds in the congruence, for each number of unrollings and each
computation at the limit. -/
structure Rules.Sound (R : Rules S) (eqv : Free.Congruence.{0, 0, 0, w} (S.interface X) α) where
  diagram : (stop : Free (S.interface X) α) → (n : Nat) → {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → R.diagram d e →
    (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (d.run stop n env rest) (e.run stop n env rest)
  continuation : (stop : Free (S.interface X) α) → (n : Nat) → {P : Boundary Ty} →
    {Qs : Exits Ty} → {k k' : Continuation S P Qs} → R.continuation k k' →
    (r : P.At X) → (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)

variable {R : Rules S}

/-- Rules that hold in a congruence hold in each congruence that has it. -/
def Rules.Sound.map {eqv' : Free.Congruence.{0, 0, 0, v} (S.interface X) α}
    (f : {x y : Free (S.interface X) α} → eqv.Rel x y → eqv'.Rel x y) (ok : R.Sound eqv) :
    R.Sound eqv' :=
  ⟨fun stop n _ _ _ _ r env rest => f (ok.diagram stop n r env rest),
    fun stop n _ _ _ _ r a rest => f (ok.continuation stop n r a rest)⟩

mutual

/-- A congruence in which each rule holds relates the two computations of each derivation. -/
def Diagram.Derivation.sound (ok : R.Sound eqv) : {Γ : List Ty} → {Qs : Exits Ty} →
    {d e : Diagram S Γ Qs} → Diagram.Derivation R d e → (env : All X Γ) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (d.run stop n env rest) (e.run stop n env rest)
  | _, _, _, _, .agree a, env, rest => eqv.agree (a.run stop n env fun r => .refl (rest r))
  | _, _, _, _, .rule r, env, rest => ok.diagram stop n r env rest
  | _, _, _, _, .symm h, env, rest => eqv.symm (Diagram.Derivation.sound ok h env rest)
  | _, _, _, _, .trans h k, env, rest =>
      eqv.trans (Diagram.Derivation.sound ok h env rest) (Diagram.Derivation.sound ok k env rest)
  | _, _, _, _, .step call each, env, rest =>
      eqv.request ⟨call.1, env.select call.2⟩ fun r =>
        Diagram.Derivation.sound ok (each r.1) (r.2.append env) rest
  | _, _, _, _, .seq (first' := first') (next := next) head tail, env, rest =>
      eqv.trans
        (Diagram.Derivation.sound ok head env
          (Exits.At.elim (fun k => next.run stop n k rest) rest))
        (first'.runRel stop n eqv env
          (Exits.At.elimRel (R := eqv.Rel)
            (fun k => Continuation.Derivation.sound ok tail k rest) (fun q => eqv.refl (rest q))))

def Continuation.Derivation.sound (ok : R.Sound eqv) : {P : Boundary Ty} → {Qs : Exits Ty} →
    {k k' : Continuation S P Qs} → Continuation.Derivation R k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)
  | _, _, _, _, .agree a, r, rest => eqv.agree (a.run stop n r fun q => .refl (rest q))
  | _, _, _, _, .rule j, r, rest => ok.continuation stop n j r rest
  | _, _, _, _, .symm h, r, rest => eqv.symm (Continuation.Derivation.sound ok h r rest)
  | _, _, _, _, .trans h j, r, rest =>
      eqv.trans (Continuation.Derivation.sound ok h r rest)
        (Continuation.Derivation.sound ok j r rest)
  | _, _, _, _, .copair cases, r, rest => Diagram.Derivation.sound ok (cases r.1) r.2 rest
  | _, _, _, _, .frame (shared' := shared') (next := next) kept args body tail, r, rest =>
      eqv.trans
        (Diagram.Derivation.sound ok body (r.2.select (args r.1))
          (Exits.At.only fun out =>
            next.run stop n ⟨Boundary.pair (kept r.1).1 out.1,
              out.2.append (r.2.select (kept r.1).2)⟩ rest))
        (shared'.runRel stop n eqv (r.2.select (args r.1))
          (Exits.At.onlyRel (R := eqv.Rel) fun out =>
            Continuation.Derivation.sound ok tail
              ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (r.2.select (kept r.1).2)⟩ rest))
  | _, _, _, _, .loop (body' := body') same, r, rest =>
      Continuation.unrolledRel (R := eqv.Rel) (eqv.refl stop)
        (fun k {again _} loops =>
          eqv.trans (Continuation.Derivation.sound ok same k (Exits.At.elim again rest))
            (body'.runRel stop n eqv k
              (Exits.At.elimRel (R := eqv.Rel) loops (fun q => eqv.refl (rest q)))))
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

/-- The frame of one context, as a diagram in that context: the exit to the boundary with that
one case, and then the frame. -/
def Diagram.framed {Γ Δ : List Ty} {M K : Boundary Ty} {Qs : Exits Ty} (kept : M.At (Port Γ))
    (args : PortMap Γ Δ) (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) :
    Diagram S Γ Qs :=
  .seq (.exit (Exits.At.here ⟨Boundary.only Γ, PortMap.id Γ⟩))
    (.frame (Boundary.family (F := fun Γ => M.At (Port Γ)) (.cons kept .nil))
      (Boundary.family (F := fun Γ => PortMap Γ Δ) (.cons args .nil)) shared next)

/-- The frame of one case of the entry of a frame, as a diagram in the context of that
case. -/
def Continuation.frameAt {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (next : Continuation S (M.product K) Qs) (c : P.Case) :
    Diagram S c.1 Qs :=
  Diagram.framed (kept c) (args c) shared next

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

/-- The step equation of a frame: a frame of a step is the step at the ports that the entry
gives, and then the frame of the diagram of each response. The kept ports go past the step. -/
inductive Continuation.FrameStep : {P : Boundary Ty} → {Qs : Exits Ty} →
    Continuation S P Qs → Continuation S P Qs → Type where
  | step {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
      (call : (S.interface (Port Δ)).Shape)
      (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Δ) [K])
      (next : Continuation S (M.product K) Qs) :
      Continuation.FrameStep (.frame kept args (.step call rest) next)
        (.copair fun p => .step ⟨call.1, (args p).select call.2⟩ fun c =>
          Diagram.framed ⟨(kept p).1, PortMap.weaken c.1 (kept p).2⟩ ((args p).lift c.1)
            (rest c) next)

/-- The exit equation of a frame: a frame of an exit is the continuation at the pair of the
kept case and the case of the exit, with the ports of the exit and the kept ports. -/
inductive Continuation.FrameExit : {P : Boundary Ty} → {Qs : Exits Ty} →
    Continuation S P Qs → Continuation S P Qs → Type where
  | exit {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
      (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
      (c : K.Case) (ports : PortMap Δ c.1) (next : Continuation S (M.product K) Qs) :
      Continuation.FrameExit (.frame kept args (.exit (Exits.At.here ⟨c, ports⟩)) next)
        (.copair fun p =>
          Diagram.rename (((args p).select ports).append (kept p).2)
            (next.atCase (Boundary.pair (kept p).1 c)))

/-- The interchange equation set. -/
def Rules.interchange (S : Signature Ty) : Rules S := ⟨Diagram.Interchange, fun _ _ => Empty⟩

/-- The interchange rule and the equations of the control sum: the two exit equations, the
composite equation, the frame equation, the case equation, and the step equation and the exit
equation of a frame. -/
def Rules.control (S : Signature Ty) : Rules S :=
  ⟨fun d e => Diagram.Interchange d e ⊕
      (Diagram.ExitCopair d e ⊕ (Diagram.ExitPast d e ⊕ Diagram.SeqExits d e)),
    fun k k' => Continuation.FrameCopair k k' ⊕
      (Continuation.CopairCases k k' ⊕
        (Continuation.FrameStep k k' ⊕ Continuation.FrameExit k k'))⟩

/-- A map out of a sum is fixed by its cases: two continuations that have a derivation at each
case have a derivation. -/
def Continuation.Derivation.ofCases {K : Boundary Ty} {Qs : Exits Ty}
    {k k' : Continuation S K Qs}
    (each : (c : K.Case) → Diagram.Derivation (Rules.control S) (k.atCase c) (k'.atCase c)) :
    Continuation.Derivation (Rules.control S) k k' :=
  .trans (.rule (Sum.inr (Sum.inl (.cases k))))
    (.trans (.copair each) (.symm (.rule (Sum.inr (Sum.inl (.cases k'))))))

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

/-- The interchange rule holds after the substitution of each implementation in which each
pure operation returns without a call. The pure step gives its response to the rest in each
order, and the two contexts of the rest have the same values. -/
def Diagram.Interchange.sound
    (pure : ImplDep (S.pureSpec X) (DepPoly.noCall.{u, v, w', z'} D) impl)
    {Γ : List Ty} {Qs : Exits Ty} :
    {d e : Diagram S Γ Qs} → Diagram.Interchange d e → (env : All X Γ) →
    (rest : Qs.At X → Free (S.interface X) α) →
    Free.Agreement ((d.run stop n env rest).subst impl) ((e.run stop n env rest).subst impl)
  | _, _, .swap a b (.inl central) first second after, env, rest =>
      let pa := pure ⟨a, env.select first⟩ central
      let ra := pa.returned.1
      ((pa.returnedBind fun r =>
          (impl ⟨b, (r.2.append env).select (second.weaken _)⟩).bind fun rb =>
            ((after r.1 rb.1).run stop n (rb.2.append (r.2.append env)) rest).subst impl).trans
        (Diagram.callWeaken b second ra.2 env fun rb =>
          ((after ra.1 rb.1).run stop n (rb.2.append (ra.2.append env))
            rest).subst impl)).trans
        (Free.Agreement.bind (.refl (impl ⟨b, env.select second⟩)) fun rb =>
          (((Diagram.callWeaken a first rb.2 env fun r =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after r.1 rb.1)).run stop n
                (r.2.append (rb.2.append env)) rest).subst impl).trans
            (pa.returnedBind fun r =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after r.1 rb.1)).run stop n
                (r.2.append (rb.2.append env)) rest).subst impl)).trans
            (Diagram.swapRest stop n (after ra.1 rb.1) ra.2 rb.2 env rest)).symm)
  | _, _, .swap a b (.inr central) first second after, env, rest =>
      let pb := pure ⟨b, env.select second⟩ central
      let rb := pb.returned.1
      (Free.Agreement.bind (.refl (impl ⟨a, env.select first⟩)) fun ra =>
          (Diagram.callWeaken b second ra.2 env fun r =>
            ((after ra.1 r.1).run stop n (r.2.append (ra.2.append env)) rest).subst impl).trans
          (pb.returnedBind fun r =>
            ((after ra.1 r.1).run stop n (r.2.append (ra.2.append env)) rest).subst impl)).trans
        (((pb.returnedBind fun r =>
            (impl ⟨a, (r.2.append env).select (first.weaken _)⟩).bind fun ra =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after ra.1 r.1)).run stop n
                (ra.2.append (r.2.append env)) rest).subst impl).trans
          ((Diagram.callWeaken a first rb.2 env fun ra =>
              ((Diagram.rename (PortMap.exchange _ _ Γ) (after ra.1 rb.1)).run stop n
                (ra.2.append (rb.2.append env)) rest).subst impl).trans
            (Free.Agreement.bind (.refl (impl ⟨a, env.select first⟩)) fun ra =>
              Diagram.swapRest stop n (after ra.1 rb.1) ra.2 rb.2 env
                rest))).symm)

/-- The first exit equation of the control sum holds in each congruence. -/
def Diagram.ExitCopair.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.ExitCopair d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (d.run stop n env rest) (e.run stop n env rest)
  | _, _, .exit c ρ each, env, rest =>
      eqv.symm (eqv.agree (Diagram.renameRun stop n ρ (each c) env rest))

/-- The second exit equation of the control sum holds in each congruence. The two computations
are one computation. -/
def Diagram.ExitPast.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.ExitPast d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (d.run stop n env rest) (e.run stop n env rest)
  | _, _, .exit out _, env, rest => eqv.refl (rest (out.select env))

/-- The composite equation of the control sum holds in each congruence. -/
def Diagram.SeqExits.sound {Γ : List Ty} {Qs : Exits Ty} : {d e : Diagram S Γ Qs} →
    Diagram.SeqExits d e → (env : All X Γ) → (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (d.run stop n env rest) (e.run stop n env rest)
  | _, _, .seq first next, env, rest => eqv.agree (Diagram.seqAtExits stop n first next env rest)

/-- The frame equation of the control sum holds in each congruence. The frame of one case has
the values that the identity port map selects. -/
def Continuation.FrameCopair.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.FrameCopair k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)
  | _, _, .frame kept args shared next, r, rest =>
      eqv.agree
        (.ofIdentity
          (Identity.cong
            (fun (values : All X r.1.1) =>
              shared.run stop n (values.select (args r.1)) (Exits.At.only fun out =>
                next.run stop n
                  ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (values.select (kept r.1).2)⟩
                  rest))
            (PortMap.selectId r.2).symm))

/-- The case equation of the control sum holds in each congruence. The case has the values
that the identity port map selects. -/
def Continuation.CopairCases.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.CopairCases k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)
  | _, _, .cases next, r, rest =>
      eqv.agree
        (.ofIdentity
          (Identity.cong (fun (values : All X r.1.1) => next.run stop n ⟨r.1, values⟩ rest)
            (PortMap.selectId r.2).symm))

/-- The step equation of a frame holds in each congruence. The frame of the diagram of a
response has the values that the lifted port map and the weakened kept ports select. -/
def Continuation.FrameStep.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.FrameStep k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)
  | _, _, .step (M := M) (K := K) kept args call after next, r, rest =>
      eqv.agree
        (Identity.transport
          (fun operands => Free.Agreement
            (.request (C := S.interface X) ⟨call.1, operands⟩ fun resp =>
              (after resp.1).run stop n (resp.2.append (r.2.select (args r.1)))
                (Exits.At.only fun out =>
                  next.run stop n
                    ⟨Boundary.pair (kept r.1).1 out.1, out.2.append (r.2.select (kept r.1).2)⟩
                    rest))
            (.request (C := S.interface X) ⟨call.1, r.2.select ((args r.1).select call.2)⟩
              fun resp =>
                (Diagram.framed (M := M) ⟨(kept r.1).1, PortMap.weaken resp.1.1 (kept r.1).2⟩
                  ((args r.1).lift resp.1.1) (after resp.1) next).run stop n
                  (resp.2.append r.2) rest))
          (All.selectSelect r.2 (args r.1) call.2)
          (.request _ fun resp =>
            ((after resp.1).runCongr stop n (resp.2.append (r.2.select (args r.1)))
                (Exits.At.onlyRel (R := Free.Agreement) fun out =>
                  .ofIdentity
                    (Identity.cong
                      (fun vals => next.run stop n
                        ⟨Boundary.pair (kept r.1).1 out.1, out.2.append vals⟩ rest)
                      ((Identity.cong
                          (fun e => All.select e (PortMap.weaken resp.1.1 (kept r.1).2))
                          (PortMap.selectId (resp.2.append r.2))).trans
                        (PortMap.selectWeaken resp.2 r.2 (kept r.1).2)).symm))).trans
              (.ofIdentity
                (Identity.cong
                  (fun e => (after resp.1).run stop n e
                    (Exits.At.only fun out =>
                      next.run stop n
                        ⟨Boundary.pair (kept r.1).1 out.1,
                          out.2.append
                            (((resp.2.append r.2).select (PortMap.id _)).select
                              (PortMap.weaken resp.1.1 (kept r.1).2))⟩
                        rest))
                  ((Identity.cong (fun e => All.select e ((args r.1).lift resp.1.1))
                      (PortMap.selectId (resp.2.append r.2))).trans
                    (PortMap.selectLift resp.2 r.2 (args r.1))).symm))))

/-- The exit equation of a frame holds in each congruence. The case of the continuation has
the values that the ports of the exit and the kept ports select. -/
def Continuation.FrameExit.sound {P : Boundary Ty} {Qs : Exits Ty} :
    {k k' : Continuation S P Qs} → Continuation.FrameExit k k' → (r : P.At X) →
    (rest : Qs.At X → Free (S.interface X) α) →
    eqv.Rel (k.run stop n r rest) (k'.run stop n r rest)
  | _, _, .exit kept args c ports next, r, rest =>
      eqv.symm (eqv.agree
        ((Diagram.renameRun stop n (((args r.1).select ports).append (kept r.1).2)
            (next.atCase (Boundary.pair (kept r.1).1 c)) r.2 rest).trans
          (.ofIdentity
            (Identity.cong
              (fun vals => next.run stop n ⟨Boundary.pair (kept r.1).1 c, vals⟩ rest)
              ((PortMap.selectId _).trans
                ((All.selectAppend r.2 ((args r.1).select ports) (kept r.1).2).trans
                  (Identity.cong (fun v => All.append v (r.2.select (kept r.1).2))
                    (All.selectSelect r.2 (args r.1) ports))))))))

/-- The interchange equation set holds after the substitution of each implementation in which
each pure operation returns without a call. -/
def Rules.Sound.interchange
    (pure : ImplDep (S.pureSpec X) (DepPoly.noCall.{u, v, w', z'} D) impl) :
    (Rules.interchange S).Sound (Free.Congruence.subst (α := α) impl) :=
  ⟨fun stop n => Diagram.Interchange.sound stop n pure, fun _ _ => fun r => nomatch r⟩

/-- The control equation set holds in each congruence in which the interchange rule holds. -/
def Rules.Sound.withControl (inter : (Rules.interchange S).Sound eqv) :
    (Rules.control S).Sound eqv :=
  ⟨fun stop n => fun r => match r with
    | .inl i => inter.diagram stop n i
    | .inr (.inl x) => Diagram.ExitCopair.sound stop n x
    | .inr (.inr (.inl x)) => Diagram.ExitPast.sound stop n x
    | .inr (.inr (.inr x)) => Diagram.SeqExits.sound stop n x,
    fun stop n => fun r => match r with
    | .inl x => Continuation.FrameCopair.sound stop n x
    | .inr (.inl x) => Continuation.CopairCases.sound stop n x
    | .inr (.inr (.inl x)) => Continuation.FrameStep.sound stop n x
    | .inr (.inr (.inr x)) => Continuation.FrameExit.sound stop n x⟩

/-- The control equation set holds after the substitution of each implementation in which each
pure operation returns without a call. -/
def Rules.Sound.control
    (pure : ImplDep (S.pureSpec X) (DepPoly.noCall.{u, v, w', z'} D) impl) :
    (Rules.control S).Sound (Free.Congruence.subst (α := α) impl) :=
  .withControl (.interchange pure)

/-- A map of rule sets: each rule of the first set is a rule of the second set. -/
structure Rules.Map (R T : Rules S) where
  diagram : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} → R.diagram d e →
    T.diagram d e
  continuation : {P : Boundary Ty} → {Qs : Exits Ty} → {k k' : Continuation S P Qs} →
    R.continuation k k' → T.continuation k k'

/-- The sum of two rule sets: a rule of the sum is a rule of one of the two sets. -/
def Rules.sum (R T : Rules S) : Rules S :=
  ⟨fun d e => R.diagram d e ⊕ T.diagram d e,
    fun k k' => R.continuation k k' ⊕ T.continuation k k'⟩

/-- The identity map of a rule set. -/
def Rules.Map.id (R : Rules S) : Rules.Map R R := ⟨fun r => r, fun r => r⟩

/-- The map of the first set into a sum. -/
def Rules.Map.inl (R T : Rules S) : Rules.Map R (R.sum T) := ⟨Sum.inl, Sum.inl⟩

/-- The map of the second set into a sum. -/
def Rules.Map.inr (R T : Rules S) : Rules.Map T (R.sum T) := ⟨Sum.inr, Sum.inr⟩

/-- A sum of two rule sets holds in each congruence in which the two sets hold. -/
def Rules.Sound.sum {T : Rules S} (left : R.Sound eqv) (right : T.Sound eqv) :
    (R.sum T).Sound eqv :=
  ⟨fun stop n => fun r => match r with
    | .inl x => left.diagram stop n x
    | .inr x => right.diagram stop n x,
    fun stop n => fun r => match r with
    | .inl x => left.continuation stop n x
    | .inr x => right.continuation stop n x⟩

mutual

/-- A derivation in a rule set is a derivation in each rule set that has its rules. -/
def Diagram.Derivation.map {T : Rules S} (f : Rules.Map R T) : {Γ : List Ty} →
    {Qs : Exits Ty} → {d e : Diagram S Γ Qs} → Diagram.Derivation R d e →
    Diagram.Derivation T d e
  | _, _, _, _, .agree a => .agree a
  | _, _, _, _, .rule r => .rule (f.diagram r)
  | _, _, _, _, .symm h => .symm (Diagram.Derivation.map f h)
  | _, _, _, _, .trans h k => .trans (Diagram.Derivation.map f h) (Diagram.Derivation.map f k)
  | _, _, _, _, .step call each => .step call fun c => Diagram.Derivation.map f (each c)
  | _, _, _, _, .seq head tail =>
      .seq (Diagram.Derivation.map f head) (Continuation.Derivation.map f tail)

def Continuation.Derivation.map {T : Rules S} (f : Rules.Map R T) : {P : Boundary Ty} →
    {Qs : Exits Ty} → {k k' : Continuation S P Qs} → Continuation.Derivation R k k' →
    Continuation.Derivation T k k'
  | _, _, _, _, .agree a => .agree a
  | _, _, _, _, .rule r => .rule (f.continuation r)
  | _, _, _, _, .symm h => .symm (Continuation.Derivation.map f h)
  | _, _, _, _, .trans h j =>
      .trans (Continuation.Derivation.map f h) (Continuation.Derivation.map f j)
  | _, _, _, _, .copair cases => .copair fun c => Diagram.Derivation.map f (cases c)
  | _, _, _, _, .frame kept args body tail =>
      .frame kept args (Diagram.Derivation.map f body) (Continuation.Derivation.map f tail)
  | _, _, _, _, .loop same => .loop (Continuation.Derivation.map f same)

end

/-- A diagram in a context with kept ports: the recursion on a diagram along a port map. A
step is the step at the ports that the port map gives, with the kept ports past it. `onExit`
gives the diagram of an exit, and `onSeq` gives the diagram of a composite. -/
def Diagram.plug {Ξ : List Ty} {Qs Qs' : Exits Ty}
    (onExit : {Γ : List Ty} → PortMap Γ Ξ → Qs.At (Port Γ) → Diagram S Γ Qs')
    (onSeq : {Γ Δ : List Ty} → PortMap Γ Ξ → PortMap Γ Δ → Diagram S Δ Qs → Diagram S Γ Qs') :
    {Γ Δ : List Ty} → PortMap Γ Ξ → PortMap Γ Δ → Diagram S Δ Qs → Diagram S Γ Qs'
  | _, _, ξ, args, .exit out => onExit ξ (out.select args)
  | _, _, ξ, args, .step call rest =>
      .step ⟨call.1, args.select call.2⟩ fun c =>
        Diagram.plug onExit onSeq (PortMap.weaken c.1 ξ) (args.lift c.1) (rest c)
  | _, _, ξ, args, .seq first next => onSeq ξ args (.seq first next)

/-- A function of diagrams that has the equation of the recursion at an exit, at a step, and
at a composite has a derivation to the recursion. -/
def Diagram.Derivation.plug {T : Rules S} {Ξ : List Ty} {Qs Qs' : Exits Ty}
    (onExit : {Γ : List Ty} → PortMap Γ Ξ → Qs.At (Port Γ) → Diagram S Γ Qs')
    (onSeq : {Γ Δ : List Ty} → PortMap Γ Ξ → PortMap Γ Δ → Diagram S Δ Qs → Diagram S Γ Qs')
    (F : {Γ Δ : List Ty} → PortMap Γ Ξ → PortMap Γ Δ → Diagram S Δ Qs → Diagram S Γ Qs')
    (atExit : {Γ Δ : List Ty} → (ξ : PortMap Γ Ξ) → (args : PortMap Γ Δ) →
      (out : Qs.At (Port Δ)) →
      Diagram.Derivation T (F ξ args (.exit out)) (onExit ξ (out.select args)))
    (atStep : {Γ Δ : List Ty} → (ξ : PortMap Γ Ξ) → (args : PortMap Γ Δ) →
      (call : (S.interface (Port Δ)).Shape) →
      (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Δ) Qs) →
      Diagram.Derivation T (F ξ args (.step call rest))
        (.step ⟨call.1, args.select call.2⟩ fun c =>
          F (PortMap.weaken c.1 ξ) (args.lift c.1) (rest c)))
    (atSeq : {Γ Δ : List Ty} → (ξ : PortMap Γ Ξ) → (args : PortMap Γ Δ) →
      (d : Diagram S Δ Qs) → Diagram.Derivation T (F ξ args d) (onSeq ξ args d)) :
    {Γ Δ : List Ty} → (ξ : PortMap Γ Ξ) → (args : PortMap Γ Δ) → (d : Diagram S Δ Qs) →
    Diagram.Derivation T (F ξ args d) (Diagram.plug onExit onSeq ξ args d)
  | _, _, ξ, args, .exit out => atExit ξ args out
  | _, _, ξ, args, .step call rest =>
      .trans (atStep ξ args call rest)
        (.step ⟨call.1, args.select call.2⟩ fun c =>
          Diagram.Derivation.plug onExit onSeq F atExit atStep atSeq (PortMap.weaken c.1 ξ)
            (args.lift c.1) (rest c))
  | _, _, ξ, args, .seq first next => atSeq ξ args (.seq first next)

/-- The exit of a diagram with the rest in line: the diagram of the pair of the kept case and
the case of the exit, at the ports of the exit and the kept ports. -/
def Diagram.inlineExit {M K : Boundary Ty} {Qs : Exits Ty} (j : M.Case)
    (each : (p : (M.product K).Case) → Diagram S p.1 Qs) {Γ : List Ty} (ξ : PortMap Γ j.1)
    (out : Exits.At [K] (Port Γ)) : Diagram S Γ Qs :=
  Exits.At.only (fun k => Diagram.rename (k.2.append ξ) (each (Boundary.pair j k.1))) out

/-- A diagram with one boundary in a context, with the rest in line: each exit has the diagram
of the pair of the kept case and its case. Each step has the kept ports past it. A composite
stays in a frame. -/
def Diagram.inline {M K : Boundary Ty} {Qs : Exits Ty} (j : M.Case)
    (each : (p : (M.product K).Case) → Diagram S p.1 Qs) {Γ Δ : List Ty} (ξ : PortMap Γ j.1)
    (args : PortMap Γ Δ) (d : Diagram S Δ [K]) : Diagram S Γ Qs :=
  Diagram.plug (Ξ := j.1) (fun ξ out => Diagram.inlineExit j each ξ out)
    (fun ξ args d => Diagram.framed (M := M) ⟨j, ξ⟩ args d (.copair each)) ξ args d

/-- The rest of a diagram with one exit case, for one kept context: the diagram of the pair of
the two cases. -/
def Diagram.restOne {Γ Δ : List Ty} {Qs : Exits Ty} (d : Diagram S (Δ ++ Γ) Qs) :
    (p : ((Boundary.one Γ).product (.one Δ)).Case) → Diagram S p.1 Qs :=
  Boundary.family (F := fun Θ => Diagram S Θ Qs) (.cons d .nil)

section Inline

variable {M K : Boundary Ty} {Qs : Exits Ty} (j : M.Case)

/-- The frame of a step is the step, and then the frame of the diagram of each response. -/
def Diagram.framedStep (next : Continuation S (M.product K) Qs) {Γ Δ : List Ty}
    (ξ : PortMap Γ j.1) (args : PortMap Γ Δ) (call : (S.interface (Port Δ)).Shape)
    (rest : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Δ) [K]) :
    Diagram.Derivation (Rules.control S)
      (Diagram.framed (M := M) ⟨j, ξ⟩ args (.step call rest) next)
      (.step ⟨call.1, args.select call.2⟩ fun c =>
        Diagram.framed (M := M) ⟨j, PortMap.weaken c.1 ξ⟩ (args.lift c.1) (rest c) next) :=
  Diagram.Derivation.trans (R := Rules.control S)
    (Diagram.Derivation.seq (R := Rules.control S) (.agree (Diagram.Agreement.refl _))
      (Continuation.Derivation.rule (R := Rules.control S)
        (Sum.inr (Sum.inr (Sum.inl (Continuation.FrameStep.step _ _ call rest next))))))
    (Diagram.Derivation.trans (R := Rules.control S)
      (Diagram.Derivation.rule (R := Rules.control S)
        (Sum.inr (Sum.inl (Diagram.ExitCopair.exit (Boundary.only Γ) (PortMap.id Γ) _))))
      (.agree (Diagram.renameId _)))

variable (each : (p : (M.product K).Case) → Diagram S p.1 Qs)

/-- The frame of an exit with a copairing is the diagram of the pair case, in line. -/
def Diagram.framedExit {Γ Δ : List Ty} (ξ : PortMap Γ j.1) (args : PortMap Γ Δ)
    (out : Exits.At [K] (Port Δ)) :
    Diagram.Derivation (Rules.control S)
      (Diagram.framed (M := M) ⟨j, ξ⟩ args (.exit out) (.copair each))
      (Diagram.inlineExit j each ξ (out.select args)) :=
  Elem.consCases
    (motive := fun (Q : Boundary Ty) (i : Elem Q [K]) => (q : Q.At (Port Δ)) →
      Diagram.Derivation (Rules.control S)
        (Diagram.framed (M := M) ⟨j, ξ⟩ args (.exit ⟨Q, i, q⟩) (.copair each))
        (Diagram.inlineExit j each ξ (Exits.At.select ⟨Q, i, q⟩ args)))
    out.2.1
    (fun q =>
      Diagram.Derivation.trans (R := Rules.control S)
        (Diagram.Derivation.seq (R := Rules.control S) (.agree (Diagram.Agreement.refl _))
          (Continuation.Derivation.rule (R := Rules.control S)
            (Sum.inr (Sum.inr (Sum.inr
              (Continuation.FrameExit.exit _ _ q.1 q.2 (.copair each)))))))
        (Diagram.Derivation.trans (R := Rules.control S)
          (Diagram.Derivation.rule (R := Rules.control S)
            (Sum.inr (Sum.inl (Diagram.ExitCopair.exit (Boundary.only Γ) (PortMap.id Γ) _))))
          (Diagram.Derivation.trans (R := Rules.control S) (.agree (Diagram.renameId _))
            (Diagram.Derivation.trans (R := Rules.control S)
              (Diagram.Derivation.rule (R := Rules.control S)
                (Sum.inr (Sum.inl
                  (Diagram.ExitCopair.exit (Boundary.pair j q.1)
                    (All.select ((args.select q.2).append ξ) (PortMap.id _)) each))))
              (.agree
                (Diagram.Agreement.renamePorts (each (Boundary.pair j q.1))
                  (PortMap.selectId ((args.select q.2).append ξ))))))))
    (fun _ i _ => i.ofNil)
    out.2.2

/-- A frame with a copairing is the diagram in the context, with the rest in line. -/
def Diagram.framedInline {Γ Δ : List Ty} (ξ : PortMap Γ j.1) (args : PortMap Γ Δ)
    (d : Diagram S Δ [K]) :
    Diagram.Derivation (Rules.control S)
      (Diagram.framed (M := M) ⟨j, ξ⟩ args d (.copair each)) (Diagram.inline j each ξ args d) :=
  Diagram.Derivation.plug (T := Rules.control S) (Ξ := j.1)
    (fun ξ out => Diagram.inlineExit j each ξ out)
    (fun ξ args d => Diagram.framed (M := M) ⟨j, ξ⟩ args d (.copair each))
    (fun ξ args d => Diagram.framed (M := M) ⟨j, ξ⟩ args d (.copair each))
    (fun ξ args out => Diagram.framedExit j each ξ args out)
    (fun ξ args call rest => Diagram.framedStep j (.copair each) ξ args call rest)
    (fun _ _ _ => .agree (Diagram.Agreement.refl _)) ξ args d

/-- A derivation between two diagrams with one boundary gives a derivation between the two
diagrams in a context, each with the rest in line. The rule set has the control equations. -/
def Diagram.Derivation.inline {T : Rules S} (control : Rules.Map (Rules.control S) T)
    {Γ Δ : List Ty} {l r : Diagram S Δ [K]} (h : Diagram.Derivation T l r)
    (ξ : PortMap Γ j.1) (args : PortMap Γ Δ) :
    Diagram.Derivation T (Diagram.inline j each ξ args l) (Diagram.inline j each ξ args r) :=
  Diagram.Derivation.trans (R := T)
    (Diagram.Derivation.symm ((Diagram.framedInline j each ξ args l).map control))
    (Diagram.Derivation.trans (R := T)
      (Diagram.Derivation.seq (R := T) (.agree (Diagram.Agreement.refl _))
        (Continuation.Derivation.frame (R := T) _ _ h
          (.agree (Continuation.Agreement.refl (.copair each)))))
      ((Diagram.framedInline j each ξ args r).map control))

end Inline

end Draft
