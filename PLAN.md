# Compiler implementation roadmap

[CONCEPT.md](CONCEPT.md) fixes the premises and defines the design.
[NOTES.md](NOTES.md) gives the observations and source contracts that the
stages must establish. [AGENTS.md](AGENTS.md) gives the binding
constructivity and verification rules. This document defines the
modules, the stages with their exit conditions, and the status of each stage.

## Modules

The implementation namespace is `Draft.*`. Foundations are in `Prelude`.

| Module family | Responsibility |
| --- | --- |
| `Prelude.Identity`, `Prelude.Indexed`, `Prelude.Decision`, `Prelude.Relation` | Shared identity eliminators, indexed finite data, decisions, and structural relations |
| `Prelude.Container` and its submodules | Shared polynomial interfaces, lenses, sums, products, families, composition, reindexing, one-call dependent evidence, `Free` computations, implementations, and their structural laws; comonoids for composition with their homomorphisms, and the state object with its lawful lenses |
| `Prelude.Container.Section`, `Prelude.Container.Verified` | Shared `DepPoly`, `FreeDep`, verified implementations and composition |
| `Prelude.Container.Runtime` | The interface with a runtime, machines, the computation with a runtime at each call, the graph of a machine, the specification with an invariant of the runtime, the machine of a part of the runtime along a lens, and the interface and the machine of a cell with the equations of global state |
| `Draft.Implementation` | Compiler operation interfaces with their specifications, and their verified implementations |
| `Draft.Diagram` | The one diagram syntax: signatures of pure and effectful operations, contexts and boundaries with their structural maps, diagrams with exits, steps, and composites, continuations with copairings, frames, and loops, the function meaning, the derivation rules of each equation set, bypasses, resolution, substitution, the laws of the loop, and structural cells and execution certificates |
| `Draft.Verified` | The interface of a diagram, the diagram as an implementation of that interface, and the map of verified implementations along a derivation |
| `Draft.Specification` | The verification over the diagram syntax: the specification of a diagram from a specification of its calls with a runtime, with the exit equations and the loop law, the evidence of each approximant and its completeness against the runs, the bound, the verified diagram, the evidence of a diagram by its constructors, the graph of a machine, the cartesian maps of a derivation, and the peel of a loop |
| `Draft.Runtime` | The runner of that syntax: the machines of a signature, the interpretation of effects with the runtime, state equations, invariant evidence, and dependent rewrite maps |
| `Draft.Stele` | The example frontend: a typed fragment of Stele, the signature of its operations, and its translation to diagrams |
| `Draft.Source` | Source diagrams as presentations of a VSDG, the relation between two presentations, the frontend interface, sharing, control, and feedback translation, and admissibility evidence |
| `Draft.Sequentialization` | The selection of a realization by cost, certified realizations, coverage, and soundness |
| `Draft.Lowering` | The backend interface, placement and storage obligations, the Stele and EVM adapters, and target refinement |
| `Draft.Checks` | Named kernel consumers and functional checks |
| `Frontend` | The translations from source languages to the fragments of `Draft`, with compiled observations. It imports the libraries of the source languages, and no module of `Draft` imports it. |
| `Observations` | Observational proofs of correctness for metatheoretical verification. They can use axioms, and no implementation module depends on them. |

The Prelude identity, indexed, decision, relation, and container modules,
`Draft.Diagram`, `Draft.Verified`, `Draft.Specification`, `Draft.Stele`, and
`Draft.Checks` exist. `Draft.Runtime` has the machines and the cell of a
signature with the equations of global state.
`Draft.Sequentialization` has the orders of the steps of a diagram, and the
list of the ready steps of a test with two cases.
The other module families are the planned locations for stages D3 to D7. The module families divide the work
and not the system: the IR is the one diagram syntax of
[CONCEPT.md](CONCEPT.md#design).

Foundations are shared through Prelude, and Draft defines no parallel
versions. Missing generic operations and laws extend their owning Prelude
modules. Generic infrastructure does not import examples, lowering, or
observations. Prelude's definitions and their dependency closures have the
same checks as compiler definitions. `Prelude.Axiom` and `Prelude.Eq` are
separate from the ordinary Prelude import and supply no compiler evidence.
Stele/EVM integration needs constructive adapters before it enters the
pipeline.

## Stages

Each stage constructs the required objects, laws, and dependent evidence. Its
examples must consume that evidence computationally and preserve the claimed
observations before the next layer uses it.
An unresolved law stays an open mathematical obligation with no axiom-backed
replacement. A stage is complete when its exit condition holds with the checks
in AGENTS.

| Stage | Deliverable and exit condition | Status |
| --- | --- | --- |
| D0. Foundation probe | Minimal polynomial maps and dependent reindexing. Composition and consumer congruence compute for a nontrivial dependent family. Identity and index transports are constructed and eliminated in the dependent consumer. | Complete |
| D1. Aberlé core | `Free`/`FreeDep`, verified composition, erasure compatibility, fold/append/concat, and distinguishable witness examples. Repeated composition preserves and exposes the supplied evidence. | Complete |
| D2. Whole diagrams with effects | Signatures of pure and effectful operations, with input ports and an output boundary for each operation. Contexts, boundaries as lists of contexts, and their structural maps: copy, discard, and exchange on ports, and the join on cases. Diagrams: exits, steps, and composites. Continuations: copairings, frames with a bypass, and loops. The static size of a diagram. The structural agreement of two diagrams whose families agree at each case, with its soundness. The request interface of a signature at a family of values, with the specification of each operation as a part of the signature. The function meaning of a diagram into `Free`, with the remaining computation as an argument, for a number of unrollings of each loop and a computation for the limit. The verification of a diagram over its function meaning, in `FreeDep`, by the constructors of the diagram: a step takes the witness of the precondition of its operation from the context, and its continuation receives the postcondition of the response. The specification of a diagram, from a specification of its calls with a runtime: a witness of the precondition of each call that a run can make, and the runs over that witness, with its two exit equations as equivalences. Each law of the stage is an agreement of function meanings for each number of unrollings, and the evidence of a verified diagram moves along it. The interchange rule for a pure step and a step that no wire connects to it, with its agreement for each lowering in which each pure operation makes no call, and with the map of verified diagrams along that agreement. The state runner, with whiskering and pure centrality. The control equation set for the state runner: the two case equations, the pointwise uniqueness of a map out of a sum, preservation by whiskering, the agreement of a composite with the diagram that has the continuation at each exit, and the agreement of a frame with the copairing that has a copy of its diagram for each case of the bypass. Branching read/write with a shared invariant, and the applicable global-state rewrite evidence. Each law is a pointwise statement, so that the graph of a function carries it to the relations of D6. The D2 checks below pass. | Complete |
| D3. Dependency orders | Source diagrams for the fixed-occurrence fragment: one sequence of steps and one exit. Each dependency-respecting order is a diagram of the same syntax with an interchange derivation from the source diagram, and its context at each step has the cut of live values. The evidence of each order is constructed from the evidence of the source along the derivation, with the condition on the specifications of the pure operations that the construction needs. Soundness for the interchange equation set: actual producer connections, exact call order, and returned-value preservation. The dependency graph of a diagram, with no names: a value is its history, and the graph has the occurrences of the steps at the histories of their operands, with the order of the effectful steps. Two calls of a pure operation with one history are one producer in the graph. The graph is thus for the interchange equation set with the copy equation set: copy naturality for each pure operation, with its soundness for each lowering in which each pure operation makes no call. The word of each order is an admissible order of the graph. The merged diagram of a diagram has one call for the equal calls of a pure operation, with a derivation from the diagram in the two equation sets, and it has no two equal occurrences. Constructive coverage for each diagram with no two equal occurrences: an arbitrary admissible order of its graph is the word of an order, with an interchange derivation and one run of each occurrence. A derivation of the interchange equation set keeps the occurrences, each the same number of times. The orders of a diagram of the fragment are a list, and each order agrees with an order of the list. The three interleavings and the shared, repeated, and discarded operand checks pass. | Current |
| D4. Control and sharing | Source diagrams with the control sum: tests as steps with one diagram for each case, copairing for values and for the runtime, joins as two exits to one case, composites for shared continuations, and guarded operations. The dependency graph of a diagram with the control sum, in which the occurrences after a test depend on its case. The decision of the identity of two histories. The relation between two presentations of one VSDG, for the order of two pure tests that no wire connects and for the case of an operation. Occurrence partitions. Figure 5.6 and the five arrangements of Figure 5.7, each as a whole diagram. Retained bypass cases are related to source control information. Tail sharing is justified with the control equation set. Reuse and speculation are justified with the copy and discard equation sets, the applicable effect equations, and dependent evidence maps. Position invariance holds for each operation that is named for discard naturality, and a guarded operation consumes the port of its case. The two sharing hypotheses of CONCEPT are tested. Soundness and coverage hold for the claimed fragment. Costs are compared under the register-machine model of the thesis, which gives the instruction counts of the source contracts. | Partial. The list of the ready steps of a test with two cases exists, with Figure 5.6 as its check. |
| D5. Substitution and composition laws | Exact silent resolution with closed cycles. Substitution with multiplied bypasses, and substitution closure. Identity and associativity with reindexing. Adequacy of finite routing certificates. Interpretation, runtime, and dependent verification commute with nested substitution. | Pending |
| D6. Feedback | Computations as Type-valued relations, with the graph of a function, composition, the control sum, and agreement as an equivalence of run families. The loop of a body as the inductive family of runs, with the initial property: the map to each relation that the body closes, and its uniqueness at each run. For a function body: the function on the inductive domain, the uniqueness of the domain evidence, the function with fuel with soundness and completeness against the runs, and domain evidence from a decreasing measure. The consequences of the initial property, each as an equivalence with its two round-trip identities: fixpoint, naturality, codiagonal, dinaturality, uniformity for pure maps, and preservation by whiskering. The transport of a postcondition that depends on the run across each law. The generic definitions extend `Prelude.Relation`. The loop of the syntax: the laws of the specification of a diagram, and the soundness and the completeness of the function meaning against the runs of the specification. The rules of the feedback equation set, with their soundness as cartesian maps of specifications. The trace as a derived operation of the loop, with the trace laws as consequences. The compatibility of a bypass with the loop, the agreement of staged execution with all-at-once execution, and cell pasting from uniformity, for the declared observation. Source loop initialization, carried values and state, guards, and exits. Invariant-preserving iteration with the domain evidence as the precondition witness. Correspondence with traced wiring and execution certificates. Feedback compatibility for a changing runtime and a preserved bypass context. The derivation of each loop choice of thesis §5.4 that the stage covers, and a statement of the work that infinite control and infinite observations still need. | Pending |
| D7. Example pipeline slice | The frontend and backend interfaces of CONCEPT, with Stele and the EVM as the instance. A source-to-target slice with compositional proof production, placement and storage accounting, and constructive Stele/EVM adapters. The declared value, effect, termination, and choice observations are preserved. The backend interpretation satisfies the named equation sets under its agreement relation. The direction from target runs to source runs gives the refinement relation of EquiVM at the boundary. The direction from source runs to target runs holds above a gas bound that exists for each source run. The lowering causes no stack underflow, no stack overflow, and no bad jump destination. The cost account uses the stack machine of EVMLean: gas for each instruction, code size, the reach of `DUP` and `SWAP`, the stack limit, and equal stack layouts at each merge. | Pending. A frontend fragment exists. |

The laws of D2 are the laws of the equation sets without feedback, and they
hold for a diagram with a loop for each number of unrollings. The source
fragments of D3 and D4 have no loop. Each realization is written
as one whole diagram, so these stages need no substitution law. D5 supplies
substitution and its laws for the stages that nest diagrams. D6 has the one
feedback structure: the loop with its laws, and the trace as a derived
operation. D5 and D6 address different termination questions.

The correspondence of a diagram with a `W′` wiring diagram is a part of D5,
and its compatibility with the loop is a part of D6. A wiring is a dependent
polynomial on the container of its boxes. A box has an operation and a
bypass. The precondition of a box is a case of its bypass, and the
postcondition of an output case is the target of that case: an exit, the
entrance of a box, or the undefined alternative. The wiring of a diagram is a
recursion on the diagram. A step is one box with its context as the bypass. A
composite gives the entrance of its continuation to each exit of its first
diagram. A frame whiskers the boxes of its diagram by its bypass. A loop
gives its entrance to each exit to that entrance, and the number of the cases
of its boundary is the bound on the hops with no box. The runs of a wiring
are over a specification of the calls, and their agreement with the
specification of the diagram is the correspondence.

Abstract categorical typeclasses are extracted only after the concrete
constructors and their laws are usable. Abstraction must not change missing
proofs into interface assumptions. The definition of done is the exit
condition and its computation evidence. It is not a number of declarations or
examples. A blocked foundational obligation blocks its consumers.

## Required checks

The [source contracts](NOTES.md#source-contracts) give the required checks of
D3 and D4. The checks below exercise the connection of control wiring,
effects, and dependent evidence.

| Check | Required evidence | Stage |
| --- | --- | --- |
| One pure operation with two inputs, one copy, and one effectful operation, in the two orders of the two steps | An interchange derivation relates the two diagrams. The two diagrams have the same meaning for arbitrary inputs and an arbitrary runtime. The context of the effectful step holds the result of the pure step. | D2 |
| Two alternatives that share state and one effectful step, in a frame with a saved control case and a saved value | Exactly the selected continuation executes. The case and the value survive the shared step. The frame and the diagram with a copy of the step in each alternative agree in each case. Reconvergence returns one updated runtime and invariant. | D2 |
| Two alternatives with one effectful continuation | The run of the composite and the run of the diagram with the continuation at each exit agree in each case, with the response evidence. | D2 |
| Pure work moved past an independent state operation | Centrality constructs the rewrite as a map of verified diagrams. Two state operations cannot be swapped without a separate effect law. | D2 |
| Read, retain a copy, write, then read again | The retained value and the new read can differ. The copy of data does not duplicate or move the original read. | D2 |
| A loop that counts down, with a pure test and one effectful step in its body | From a closed counter, the function meaning is the calls of the iterations, for an arbitrary value and each sufficient number of unrollings. With a smaller number, it ends with the computation for the limit. A run exists from each counter, for an arbitrary value and an arbitrary runtime, and the unrolling law of the loop applies to it. | D2 |
| Two pure tests that no wire connects, in the two orders | A derivation relates the two source diagrams, and the two meanings agree in each of the four cases. | D4 |
| Nested substitution with dependent box indices and nontrivial bypasses | Interpretation before and after substitution gives related requests, responses, runtime transitions, and witness-dependent postconditions. Repeated substitution consumes this evidence. | D5 |
| Closed silent routing | The resolver returns cycle evidence and no invented result. | D5 |
| Retained context around feedback | The bypass stays unchanged while successive calls receive updated runtime evidence. | D6 |
| A loop that changes the runtime, for an arbitrary initial state | The run, the result on the domain evidence from a measure, and the function with fuel agree. Unrolling changes the length of the run, and its inverse gives the first run again. | D6 |
| A postcondition that depends on the run, across unrolling | Evidence for one iteration moves to the unrolled run and back. The kernel check recovers it for an arbitrary state. | D6 |

Arbitrary position types and distinguishable precondition witnesses stay in
each check. Failure of a compatibility obligation blocks the consumers of the
affected representation.

## D0: complete

| Deliverable | Location |
| --- | --- |
| Type-valued identity and its eliminators | [Prelude/Identity.lean](Prelude/Identity.lean) |
| Polynomial maps, structural agreement, composition and congruence laws | [Prelude/Container/Core.lean](Prelude/Container/Core.lean), [Prelude/Container/Agreement.lean](Prelude/Container/Agreement.lean) |
| One-call dependent evidence and response reindexing | [Prelude/Container/Section.lean](Prelude/Container/Section.lean) |
| Kernel checks that consume routing and witness-dependent evidence | [Draft/Checks/Polynomial.lean](Draft/Checks/Polynomial.lean), [Draft/Checks/Dependent.lean](Draft/Checks/Dependent.lean) |

D0 covers closed, repeated one-call composition. It does not contain `Free`,
`FreeDep`, open-call verification, whole diagrams, or the correspondence
between runtime and source.

## D1: complete

Source: Aberlé, [Compositional Program Verification with Polynomial Functors in
Dependent Type Theory](https://arxiv.org/abs/2604.01303).
[CONCEPT.md](CONCEPT.md#aberlé-implementations-and-their-dependent-verification)
maps its labelled constructions to implementation responsibilities.

1. `Free` over a `Prelude.Container` interface: return, request, structural
   bind, and implementation substitution, with their laws stated through
   pointwise and structural relations.
2. Dependent polynomials and `FreeDep` indexed by a computation: return
   evidence, request admission evidence, and continuations that consume response
   evidence. `Prelude.Container.Evidence` is the closed one-call case.
3. Verified implementations and their composition (`sumDep`, `compDep`,
   `thm:comp-dep`), built along the same constructors as implementation
   composition, with erasure compatibility.
4. `foldInd`, relational append, and composed concat. Kernel checks recover the
   ordinary results by elimination of the relational evidence.
5. A check with two distinguishable admission witnesses for one input. Returned
   evidence enters a later request and is consumed after repeated substitution.

| Item | Definitions and laws | Kernel checks |
| --- | --- | --- |
| 1 | [Prelude/Container/Free.lean](Prelude/Container/Free.lean), with the family sum in [Prelude/Container/Core.lean](Prelude/Container/Core.lean) | [Draft/Checks/Free.lean](Draft/Checks/Free.lean) |
| 2 | `DepPoly` in [Prelude/Container/Section.lean](Prelude/Container/Section.lean), and `FreeDep` in [Prelude/Container/Verified.lean](Prelude/Container/Verified.lean) | [Draft/Checks/Verified.lean](Draft/Checks/Verified.lean) |
| 3 | `ImplDep`, substitution of evidence, composition, and copairing in [Prelude/Container/Verified.lean](Prelude/Container/Verified.lean); `DepPoly.sigma` in [Prelude/Container/Section.lean](Prelude/Container/Section.lean); `Impl.ofSection` in [Prelude/Container/Free.lean](Prelude/Container/Free.lean) | [Draft/Checks/Composite.lean](Draft/Checks/Composite.lean), [Draft/Checks/Order.lean](Draft/Checks/Order.lean) |
| 4 | The polynomial with no shape in [Prelude/Container/Core.lean](Prelude/Container/Core.lean), with its provider and evidence in [Prelude/Container/Section.lean](Prelude/Container/Section.lean) | [Draft/Checks/Fold.lean](Draft/Checks/Fold.lean) |
| 5 | The definitions of items 2 and 3 | [Draft/Checks/Verified.lean](Draft/Checks/Verified.lean), [Draft/Checks/Composite.lean](Draft/Checks/Composite.lean) |

The checks of item 2 run evidence through a branch, three binds, and the
associativity and unit agreements. The checks of item 3 run the lift of a
composite of three implementations, with a family sum, through the two cases
of its test, and they move the lift along the associativity agreement of the
composition. Each check has arbitrary responses and arbitrary admission keys.

[Draft/Checks/Fold.lean](Draft/Checks/Fold.lean) has Aberlé's fold with
`foldInd`, and three instances. Append and concat have relational
specifications, and concat calls append in its step. Their checks eliminate
the relational evidence and recover the lists, with arbitrary elements. The
third instance calls the store in its base and in each step. The witness of
its precondition is the admission of the first call, and the receipt of each
call is the key of the admission of the next call. Its checks have the two
admission constructors for one input. The fold has a second form, with each
call in the continuation of the call before it and no bind. The two forms
agree, and a lift moves along the agreement.

The checks of item 5 are in two modules. Each case of the branch and each case
of the composite lift has the two admission constructors for one input, and
the two constructors give different payloads. The receipt of one call is the
key of the admission of the next call, and the composite lift consumes it
after two substitutions.

[Draft/Checks/Order.lean](Draft/Checks/Order.lean) has two computations that
call two pure operations and one effectful operation in different orders. An
operation is pure when its implementation returns without a call. After the
substitution of the implementations, the two computations are identical by
`.refl`, and the evidence of each order gives the same payload. The check also
constructs the evidence of one order from the evidence of the other order. The
construction goes through the one computation, and it uses a condition of this
example: the specification of each pure operation fixes its response. The
construction for each diagram is the map of verified implementations along a
derivation of D2. The construction of the lift of an order, for a
specification that does not fix the response, is open for D3.

[N6](NOTES.md#n6-slow-elaboration-is-not-slow-kernel-checking) has the three
results on cost that the checks gave: the effect of `smartUnfolding`, the cost
of a generated matcher on an indexed family, and the cost of a sequence that
binds its earlier part.

## D2: complete

[Draft/Diagram.lean](Draft/Diagram.lean) has the plain part of each
construction. The verification over it is by the method of
[CONCEPT.md](CONCEPT.md#design):

- [Draft/Verified.lean](Draft/Verified.lean) has the interface of a diagram,
  and the diagram as an implementation of that interface by calls of the
  interface of its signature.
- [Draft/Specification/Verified.lean](Draft/Specification/Verified.lean) has
  the evidence of a diagram at an input, for a condition at each result of a
  run. It is the evidence of one call of the specification of the diagram
  with a bound. Each constructor of a diagram and of a continuation has its
  evidence. A step takes a witness of the precondition of its operation, and
  the diagram of each response receives the postcondition. A composite has a
  condition at the boundary of its continuation, a frame has a condition at
  the exit of its diagram, and a loop has an invariant or a family with a
  count.
- The evidence at each input with a witness of a specification, which is a
  `DepPoly` on the interface of the diagram, gives the verified
  implementation (`ImplDep`) of each approximant. The composition with a
  verified lowering is `ImplDep.trans`.
- The map of verified implementations along a derivation, for a rule set that
  holds after the substitution of the lowering.

The specification of the operations is a `DepPoly` on the request interface
of the signature. [Draft/Checks/Lift.lean](Draft/Checks/Lift.lean) has four
verified diagrams, each with a verified lowering and kernel checks that
eliminate the evidence at the exit: the two orders of a pure step and an
effectful step, with the lift of the first order moved to the second order
along the interchange derivation; one continuation of two control paths,
with a condition on the sum that each path establishes from the postcondition
of the test; one effectful step of two control paths in a frame, with the lift of the
frame moved along the frame equation to the copairing that has the frame of
each path alone; and the loop that counts down, with a family that has the
receipts of the calls, the identity of the value, and a count. Each lift has
the empty condition at the limit, so each verified implementation has an
arbitrary computation at the limit and needs no evidence for it. A witness of
the precondition of the loop shows that the counter is less than the number
of unrollings. A derivation with the interchange rule under the loop moves
the verified loop to the loop that has the effectful step before the pure
step in each iteration.

The calls with a runtime have one form.
[Prelude/Container/Runtime.lean](Prelude/Container/Runtime.lean) has the
interface with a runtime: a call has a runtime, and a response has the next
runtime, or the call stops. A machine is a closed provider of that interface,
which is Aberlé's machine with an explicit carrier. A computation gives the
computation with the runtime at each call, and an implementation gives an
implementation in the same manner. The run on a machine is the run of that
computation with the machine as the provider. A specification of the
interface with a runtime relates the runtime before a call to the response
and the runtime after it, and a relation of calls is such a specification.
The graph of a machine is the specification that has its response at each
call, and each implementation is a verified implementation between the graph
of its machine and the graph of the machine of its calls. A specification of
an interface with an invariant of the runtime gives a specification of the
interface with a runtime, and the evidence of a computation and a verified
implementation move to it.

A part of the runtime has a lens. The state object of a type has a value as a
shape and the next value as a position, and a lens is a morphism of two state
objects: its view gives the part, and its update gives the runtime with a new
part. [Prelude/Container/Comonoid.lean](Prelude/Container/Comonoid.lean) has
the data of a comonoid for the composition of containers, the homomorphisms of
comonoids with their composition, and the comonoid of a state object. A lawful
lens is a homomorphism of the comonoids of two state objects. Its counit square
is the law of the update with the view. The inner shapes of its
comultiplication square are the law of the view of an update, and its
positions are the law of two updates. The comultiplication square is an
agreement of the two layers of a composite, which needs no identity of two
functions. A machine on a part gives a machine on the whole runtime along the
lens. For a lawful lens, the run on the whole is the run on the part from the
view, with the update of the first runtime at the last value of the part. Two
computations with one run on the machine of the part thus have one run on
each machine of the whole that is that machine along the lens at their calls,
in each continuation. The module of the runtime has the interface of a cell,
which is Aberlé's `State`, with its machine, and the five equations of global
state hold on that machine by computation. A specification of an interface is
a specification of the interface with the unit runtime and no stop, at the
same universe levels, and the evidence of a computation and the evidence of
the computation with the unit runtime give each other.

The computation with a runtime has three laws, each as an agreement: it
respects agreement, the computation of a bind is the first part and then the
rest from its result, and the computation of a substitution is the
substitution of the implementation with a runtime. The laws of the run on a
machine are these laws at a provider: the run of a bind, the run of a
substitution on the machine of the implementation, and the machine of a
composite. The evidence of a bind and of a substitution moves along the two
laws. [PreludeTests/Runtime.lean](PreludeTests/Runtime.lean) has her state
invariant, a specification of two runtimes for one program, and the laws for
a computation that calls the program two times. It has a lawful lens to the
first part of a pair, the composite of two such lenses, the run of the machine
of a cell along the lens, and two computations of a cell that have one run on
a cell of pairs, in a continuation that reads the cell again. It has the
evidence of the program with the unit runtime, and the first evidence again
from it.

The evidence of a diagram has the runtime. A specification of the calls is a
`DepPoly` on the interface with a runtime, and a condition has the runtime. A
step for the graph of a machine has the response of the machine at its
runtime. A specification of a diagram with a runtime is a `DepPoly` on the
interface of the diagram with a runtime. The evidence of a diagram for it
gives the verified implementation with a runtime, and its composition with a
verified lowering with a runtime is `ImplDep.trans`. A specification with no
runtime is the case of the unit runtime, and its constructors have no
runtime.

A derivation in a rule set that holds after the substitution of a lowering
gives an agreement of the two computations with a runtime, after the lowering
with a runtime. The map of verified implementations with a runtime along the
derivation has that agreement as its plain part. Such a rule set holds on the
machine of the lowering, for each machine of the target: the two diagrams of
a derivation have one run from each context and each runtime.

A rule set can hold on a machine and not after a substitution, because the
two sides of a rule can have different calls and one run. A derivation in
such a rule set gives the identity of the machines of its two diagrams at
each call. The evidence of the machine of the first diagram moves along that
identity to the machine of the second diagram, for each specification of the
interface of the diagram with a runtime.

[Draft/Runtime.lean](Draft/Runtime.lean) has the cell of a signature at a
value type: a read with no operand and one output port, and a write with one
operand and no output port, each with the identities of its arities. The equations of global state are
five equations between closed sequences of steps of the cell, with the typing
of Román–Sobociński (`sec:exampleGlobalState`): two reads give one value, a
read whose value has no use does nothing, the last of two writes stays, a read
and then a write of its value does nothing, and a write and then a read gives
the written value. For each equation, one theorem gives the derivation for
each context, each port, and each rest, in the control equation set with the
equations of global state. Its proof is the closed equation, the theorem of
the frame, and two structural agreements.

The cell of a signature is a morphism from the interface of a cell to the
request interface of the signature, for each family of values: the typed read
and the typed write are its calls. The equation set of global state holds on
each machine that is, at the calls of the cell, the machine of a cell along a
lawful lens of the runtime. Each equation is the equation of the machine of a
cell, moved along the lens. The laws of the lens are identities of runtimes,
so a runtime that is a function is not in the scope of the theorem, and a
machine whose read or write stops or counts is not such a machine.

[Draft/Checks/State.lean](Draft/Checks/State.lean) has a cell with a read and
a write: a read, a kept value, a write, and a second read, for an arbitrary
cell, with the number of the reads; a write and a read in the two orders,
which give different values; and the first diagram with a specification of
two runtimes, whose evidence at the run on the machine a kernel check
eliminates. It has a lowering to the interface of the cell, in which the pure
operation returns without a call, and the two orders of the pure step and a
read. The interchange derivation gives the identity of the two runs on the
machine of the lowering, and it moves the verified implementation of the
first order to the second order. The specification has a lower bound of the
number of the reads in the witness of its precondition, and two witnesses of
one runtime give different payloads in each order. The run of the verified
first order on the machine of the lowering is the evidence of its machine,
and the derivation moves that evidence to the machine of the second order,
with the same payloads. The module has a second machine of the cell, whose
reads do not count: the machine of a cell along the lens of the runtime to the
value. At the calls of the cell of the signature, the machine of the lowering
to it is that machine, by computation in each of the two cases. The equations
of global state thus hold on the machine of the lowering, and the control
equation set holds on it too. Each of the five theorems of the cell has
one application, in a context with two inputs. A check consumes the identity
of the two runs of each application through a dependent payload, for
arbitrary inputs and an arbitrary runtime. The static sizes of the two sides
are 2 and 1 for two reads, 1 and 0 for a read with no use, 2 and 1 for two
writes, 2 and 0 for a read and then a write, and 2 and 1 for a write and then
a read.

[Draft/Checks/Branch.lean](Draft/Checks/Branch.lean) has the required check
of two alternatives with a frame, on a machine. The signature has a read, a
write, and a pure test. The two alternatives of the test share one read of
the cell in a frame, and the bypass keeps the alternative and one input.
After the read, the first alternative writes the kept input, and the second
alternative reads the cell again. Each run on the machine of the lowering has
the steps of its alternative only, for an arbitrary kept input and an
arbitrary runtime. The frame equation relates the frame to the copairing that
has the frame of each alternative alone, and the two forms have one run on
the machine. The specification has an invariant of the runtime: a lower bound
of the number of the reads. The machine of the cell has evidence of the
invariant, and the evidence of the diagram is built by its constructors. The
shared read takes the invariant from the entry of the frame, and the exit of
each alternative has the invariant at the last runtime. Two witnesses of one
runtime give different payloads, and the payload has the number of the reads
of the alternative. On the first alternative, the exit has the identity of
the second value with the kept input, from the fact of the test. The frame
equation moves the verified implementation to the other form, with the same
payloads. The frame has 4 steps, and the other form has 7.

The text below describes the plain part.

[Draft/Diagram.lean](Draft/Diagram.lean) has the signatures, the boundaries
as lists of contexts with their product, the port maps, the diagrams, the
continuations with the loop, the static size, and the function meaning
into `Free`.
The function meaning has a number of unrollings and a computation at the limit
of a loop. A loop with no unrolling is that computation, and a loop with one
more unrolling is its body with the loop at each exit to the entrance, by
computation. Each law of the module is a law for each number and each
computation at the limit, and its case for the loop is an induction on the
number.
The exits of a diagram are a list of boundaries, and the boundary of the
continuation of a composite is the first boundary of the exits of its first
diagram. The two exit equations of the control sum hold by computation, for
each case, each continuation, and each remaining computation. The module has
the agreement of a composite with the diagram that has the continuation at
each exit to its boundary, for each diagram and each continuation. It
has the structural agreement of two diagrams: the same form, and agreement of
the diagrams of each case. Two diagrams that agree have computations that
agree. A port map acts on a diagram, and the computation of the result is the
computation of the diagram at the selected values. The identity map and the
composite of two maps have that law for the computation. The identity law
and the composition law of the action are structural agreements of diagrams
too: the diagram with the ports of the identity map agrees with the diagram,
and two renamings agree with the renaming by the composite map. A map of exits
acts on the exits of a diagram, and a family with a diagram for each exit
case gives the diagram with those diagrams at its exits. Each of the two has
its law for the computation. The derivations of a
rule set are the smallest relation that has the rules and structural
agreement, and that is an equivalence and a congruence for each form of a
diagram and of a continuation. One theorem gives the soundness of each rule
set: a congruence of computations in which each rule holds relates the two
computations of each derivation. A congruence is a parameter of the theorem.
Agreement after the substitution of an implementation is a congruence, and
the identity of the runs on a machine from each runtime is a congruence that
has it. The interchange rule relates the two orders of two steps
that no wire connects, of which one is pure. It holds after the substitution
of each implementation in which each pure operation returns without a call.
That premise is a verified implementation. The specification of the pure
operations has the identity of the kind of an operation with the pure kind as
the witness of its precondition, and the implementation is verified for the
specification that admits no call. Evidence for that specification gives the
value that a computation returns, and the agreement of the computation with
the computation that returns it.
The equations of the control sum hold in each congruence. The two exit
equations of the control sum are rules too. An exit to the boundary of a copairing, and
then the copairing, is the diagram of the case of the exit, with renamed
ports. An exit past a continuation, and then the continuation, is that exit.
The control equation set has three more rules. A composite is the diagram
that has the continuation at each exit to its boundary. A frame is the
copairing that has the frame of each case alone: the frame has one copy of
its diagram, and the copairing has one copy for each case. A continuation is
the copairing of its cases. Each of the three holds in each implementation.
The last rule gives the uniqueness of a map out of a sum as a derivation: two
continuations that have a derivation at each case have a derivation.
The control equation set has two equations of a frame. A frame of a step is
the step at the ports that the entry gives, and then the frame of the diagram
of each response, with the kept ports past the step. A frame of an exit is its
continuation at the pair of the kept case and the case of the exit. Each of
the two holds in each congruence. They give one theorem for each rule set
that has the control equations: a derivation between two diagrams with one
boundary gives a derivation between the two diagrams in a context, each with
the rest in line at each exit. An equation between two closed sequences of
steps thus applies in each context and with each rest, by one application of
the theorem. A composite in a side of the equation stays in a frame. A map of
rule sets gives a map of derivations, and a sum of two rule sets holds in each
congruence in which the two sets hold.
[Prelude/Indexed.lean](Prelude/Indexed.lean) has the positions of a
concatenation, the case analysis of a position of a nonempty list, and the
selection of values at a list of positions, with their laws. [Prelude/Container/Section.lean](Prelude/Container/Section.lean) has the
specification that admits no call, and
[Prelude/Container/Verified.lean](Prelude/Container/Verified.lean) has the
returned value of a computation with evidence for it.

[Draft/Checks/Diagram.lean](Draft/Checks/Diagram.lean) has the plain
computations of three required checks, and three more checks, with arbitrary inputs,
arbitrary responses of the store, an arbitrary number of unrollings, and an
arbitrary computation at the limit:

- A pure operation with two inputs, whose first input has two uses, and an
  effectful operation, in the two orders of the two steps. An interchange
  derivation relates the two diagrams. After the substitution of the
  implementations, the two orders are one computation with one call. A
  diagram with other functions of the case agrees with the first diagram of
  the rule, and the derivation starts from that diagram too. The soundness of
  each of the two derivations gives the identity of the returned values, and
  a check consumes it with the response of the store. A derivation in the
  control equation set relates the diagram with an exit and a continuation
  after the two steps to the diagram with renamed ports. The interchange in
  a composite uses the congruence of a composite and of a copairing. Each
  construction of a derivation has a check with arbitrary inputs: the two
  premises of the interchange rule, the symmetry, each congruence, and the
  three laws of renaming for the computation, and the identity law and the
  composition law of renaming as agreements of diagrams.
- A pure operation and two effectful operations. Two interchanges move the
  pure step after the two effectful steps: one at the first step, and one
  after the first effectful step, by the congruence of a step. The symmetry
  of the relation moves it back. The check of the soundness has closed
  inputs, and only the kernel reduces it.
- A test with a different sum in each case, one exit case for the two paths,
  and one effectful continuation. The composite and the diagram with the
  continuation at each exit give the same values in each case of the test.
  The check consumes the identity that the agreement gives. The composite has
  4 steps, and the diagram with the continuation at each exit has 5. The
  composite equation relates the two forms as a derivation, and a check
  consumes its soundness. A second continuation has the same diagram at its
  one case. The uniqueness of a map out of a sum gives the derivation of the
  two continuations, and a check consumes its soundness.
- A test, one effectful step for the two paths, and a different sum after
  that step on each path. A frame has the one copy of the step, and its
  bypass keeps the path and one input. After the substitution, the frame and
  the diagram with a copy of the step in each path are one computation with
  one call, in each case of the test. The frame has 4 steps, and the diagram
  with a copy of the step in each path has 5. The frame equation relates the
  frame to the copairing that has the frame of each path alone, by the
  congruence of a composite. A check consumes its soundness, and that form
  has 7 steps.
- A composite in a composite. One path of the inner composite exits past the
  inner continuation, to the outer continuation. The outer composite and the
  diagram with the outer continuation at each exit of the inner composite
  give the same values in each case of the test. The check consumes the
  identity that the agreement gives. The composite has 4 steps, and the
  diagram with the continuation at each exit has 5.
- Two tests and three paths, with one effectful step for two of the paths. A
  frame has the one copy of the step, and the third path exits past the
  frame. After the substitution, the third path has no call, and each other
  path is one call. The diagram has 6 steps. A derivation in the control
  equation set relates an exit past the frame to the exit, and a check
  consumes its soundness.

[Draft/Checks/Countdown.lean](Draft/Checks/Countdown.lean) has the required
check of a loop. The body of the loop has a pure test, a pure step, and an
effectful step. From the counter 2, the function meaning with three or more
unrollings is two calls of the store, for an arbitrary value and an arbitrary
computation at the limit. With two unrollings, it is the two calls and then
the computation at the limit. The body and then the loop is the same two
calls with one unrolling less. For a function of the calls with a runtime, a
run of the loop exists from each counter, for an arbitrary value and an
arbitrary runtime. The run of the whole diagram from the counter 2 has the
value and the runtime, and the first exit equation gives its run of the loop,
with its round trip by computation. The unrolling law and the fixpoint law of
the loop apply to the run from the counter 2, and their round trips hold by
computation. The loop has 3 steps, and the body and then the loop has 6.

## D3: current

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the orders
of the steps of a diagram. A step is ready in a diagram when it can move to
the front. Its operands are ports of the context of the diagram, so no
operand is an output of a step before it. Each step before it is pure, or the
step is pure. The evidence follows the path to the step, and it has the
diagram after the step. One theorem gives the derivation from the diagram to
the diagram with the ready step at the front, for each rule set that has the
interchange rule. The derivation has one interchange for each step that the
ready step passes. The evidence of a ready step is for each diagram without a
composite: a step that is ready in each case of a test moves before the test.

An order of a diagram is a diagram with the evidence that it is an order. The
diagram is the plain part, and the evidence follows its constructors. An exit
is the source diagram. A step has the evidence that it is ready in the source
diagram, which is the witness of a precondition, and the diagram of each
output case has the evidence for the diagram after the step. The derivation
from the source diagram to an order has one application of the theorem for
each step.

[Draft/Source.lean](Draft/Source.lean) has the diagrams of the fragment with
fixed occurrences: one sequence of steps and one exit. The evidence is a
function of the diagram. The output boundary of each step has one case: the
type of its cases has a center, and each case is identical to the center. The
action of a port map keeps the fragment. For a diagram of the fragment, the
ready steps are a list, and the orders are a list: one order for each choice
of a ready step at each point. A step of the rest of the first step is ready
in the diagram when one of the two steps is pure and its operands have no
output port of the first step. The diagram after a ready step and each order
are diagrams of the fragment.
[Prelude/Indexed.lean](Prelude/Indexed.lean) has the part of a position of a
concatenation, and the search of a position of an element in a list.

[Draft/Source.lean](Draft/Source.lean) has the dependency graph of a diagram
of the fragment, with no names. A value is its history: an input of the
diagram, or an output port of the call that made it. A call has the histories
of its operands and the effectful call before it, which is the state edge of
the graph. The graph is the list of the occurrences of the steps: each step
is a call at the histories of its context, and its output ports have that
call as their history. The container of the graph has a shape for each
occurrence and a position for each operand. The occurrences of a diagram with
renamed ports are the occurrences of the diagram at the selected histories.

The graph is a specification of the runs of its steps. The runtime has the
list of the remaining occurrences and the list of the done occurrences. A run
has the number of an occurrence in the remaining list. It is admitted when
the call of each operand is done, and the effectful call before it is done.
The response has the remaining list without the occurrence and the done list
with it. A word of runs is an admissible order when it has evidence of this
specification, with no remaining occurrence at its end. Each occurrence thus
has one run.

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the theorem
of the move: a move of a ready step keeps each occurrence. The occurrences of
the diagram have the occurrence of the ready step at the number of the steps
that it passes, and the other occurrences, in their order, are the
occurrences of the diagram after the step. The proof has the law of renamed
ports, the two laws of the selection of values of the interchange proof, and
three laws of the kinds. The word of an order has that number for each step.
It is an admissible order of the occurrences of the source diagram, for each
order of each diagram of the fragment: the evidence follows the steps of the
order, with the theorem of the move as the witness of each precondition.

[Draft/Diagram.lean](Draft/Diagram.lean) has the copy rule: two calls of a
pure operation at the same ports are one call, and the rest has the output
ports of that call at the two places. The rule holds after the substitution of
each implementation in which each pure operation returns without a call, which
is the premise of the interchange rule. The copy equation set has this rule,
and the sum of two rule sets joins it to the interchange equation set.

[Draft/Source.lean](Draft/Source.lean) has the merge of the equal calls of a
diagram of the fragment: two calls of a pure operation at the same ports are
one call in the merged diagram. The merge goes through the steps one time,
with the list of the available calls and a port map to the context of the
merged diagram. It uses the decision of the identity of two operations, which
is a premise on the signature, and the decision of the identity of two ports,
which [Prelude/Indexed.lean](Prelude/Indexed.lean) has. The merged diagram has
a derivation from the source diagram in each rule set that has the
interchange rule and the copy rule. The proof is one recursion on the diagram,
for a context of diagrams that absorbs each available call. The context under
a step absorbs the call of that step by the copy rule, and it absorbs each
earlier call by one interchange.

The merged diagram is a diagram of the fragment, and its occurrences have no
element at two positions. The proof has a state of the merge at each point:
each call of a history of the context is a call of a step before, each such
call with a pure operation is an available call, each such call with an
effectful operation has less effectful calls before it than the last
effectful call has, and no history is at two ports. The call of a step that
the search does not find is thus not a call of a step before. The search
finds an available call for its own operation and ports, because a type with
a decision of identity has one identity proof for each two elements, which
[Prelude/Decision.lean](Prelude/Decision.lean) has. The theorem of the other
direction thus applies to each merged diagram.

The graph of the merged diagram has a link to the graph of the source
diagram. A position of an occurrence in the graph of the source diagram gives
a position of that occurrence in the graph of the merged diagram, and a
position in the graph of the merged diagram gives a position in the graph of
the source diagram. The occurrences of the merged diagram are thus the
occurrences of the source diagram, each one time. The proof has a link for
each available call: its call is a call of a step before, and its output
ports have the histories of the output ports of that call.

A source diagram with two equal calls keeps the two calls in each of its
orders, and each order has an interchange derivation. The theorem of its
graph is for its merged diagram, which has one occurrence for the two calls.

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the other
direction of the theorem of the graph, for a diagram of the fragment whose
occurrences have no element at two positions. The step of an admitted run is
a ready step. No operand of it is an output port of a step before it, because
the call of that step is not done. One of each two steps is pure, because the
effectful call before the step is done. An admissible order of the
occurrences is thus the word of an order, which has the ready step of each
run, and that order has an interchange derivation.
[Prelude/Indexed.lean](Prelude/Indexed.lean) has the lists with no element at
two positions.

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the theorem
of the occurrences along a derivation: a derivation of the interchange
equation set keeps the fragment, and the two diagrams have the same
occurrences, each the same number of times. The statement is a correspondence
of the positions of each occurrence in the two lists, with the two round
trips, which [Prelude/Indexed.lean](Prelude/Indexed.lean) has. The producer
connections and the one run of each occurrence are thus kept by each
derivation of the set, and not only by the orders.

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the
completeness of the list of the orders: each order of a diagram of the
fragment agrees with an order of the list. The statement is an agreement of
diagrams, because the evidence of an order has functions of the output cases,
and the list has the functions that the value at the center of the cases
gives. Each ready step is in the list of the ready steps, with a diagram
after it that agrees at each case. The proof is for each diagram that agrees
with the source diagram, and it has the view of an agreement from a step or an
exit and the agreement of two renamed diagrams, which
[Draft/Diagram.lean](Draft/Diagram.lean) has. The bound of the list is the
number of the steps, and the diagram after a ready step has one step less.
[Prelude/Indexed.lean](Prelude/Indexed.lean) has the positions in the list of
the values of a partial function and in a concatenation of lists of values.

[Draft/Checks/Dependency.lean](Draft/Checks/Dependency.lean) has the three
required checks. The first source diagram has three steps. `A` and `B` are
pure, and `B` uses the output of `A`. `C` is effectful and uses one input
only. The orders `A C B` and `C A B` are two diagrams, each with the evidence
that it is an order of the source diagram. Each order gives the same values,
for arbitrary inputs and an arbitrary response of the store. A check consumes
the soundness of the derivation of an order through a dependent payload. The
source diagram is a diagram of the fragment. Its ready steps are `A` and `C`.
The list of its orders has the three orders and no other order, and each
order of the list gives the same values. For the evidence of the three orders
that is not from the list, the theorem of the completeness gives the three
positions of the list, and a check consumes the agreement of the order
`C A B` with the order of the list through a dependent payload. The source diagram has a verified
implementation for a specification with an admission. The map of verified
implementations along the derivation of an order, which is the map of D2,
gives the verified implementation of each order. The receipt at the exit of
each of the two orders gives the payload of the source diagram through its
identity, for an arbitrary admission. A check consumes the postcondition of
`B` in the evidence of the order `C A B` through a dependent payload.

The dependency graph of the first source diagram has the occurrences of its
three steps. The orders `A C B` and `C A B` have the same occurrences in the
other order, and no occurrence changes. A check consumes the identity of the
theorem of the move of `C` through a dependent payload. The evidence that the
word of the order `C A B` is an admissible order comes from the theorem. It
runs on the machine of the runs, and a check consumes the identity that no
occurrence remains. The done occurrences at the end are the occurrences of
the order, with the last run first. The derivation of the order `C A B` keeps
the occurrences: the occurrence of `C` goes from the third position to the
first position, and a check consumes the round trip of a position through a
dependent payload. A word that starts with `B` has no
evidence, because the call of an operand of `B` is not done. No two of the
three occurrences are equal. From the evidence of the word of the order
`C A B`, the theorem of the other direction gives an order with the steps
`C A B`, and a check consumes the identity of its word through a dependent
payload.

The second source diagram has a shared operand and a repeated operand: `B`
has the output of `A` as its two operands, the effectful `C` has that output
as its operand, and `D` has the outputs of `B` and `C`. The list of its
orders has the two orders of `B` and `C`. Each order has four steps, so `A`
has one occurrence, and each gives the same values. The third source diagram
has a discarded value: no step and no exit port has the response of the
effectful `A`. The list of its orders has the two orders of `A` and the pure
`B`, and each order is one call of the store after the lowering.

The fourth source diagram has two equal calls: the pure `A` has two calls at
the two inputs, and `D` has the outputs of the two calls. The copy rule
relates it to the diagram with one call of `A`, in which `D` has the output of
that call two times. The two diagrams give the same values, and a check
consumes the soundness of the rule through a dependent payload. A second
check does this for a rest with two steps, and its payload has the response
of the store. In the graph,
the two calls are one occurrence two times, and the two operands of `D` have
one history. The list of the orders has the two orders of the two calls. The
word that runs one call of `A`, then `D`, and then the other call of `A` is an
admissible order of the occurrences, and it is not the word of an order. Its
evidence runs on the machine of the runs, and a check consumes the identity
that no occurrence remains. The merged diagram of the fourth source diagram
has one call of `A`. It gives the same values, and a check consumes the
soundness of its derivation through a dependent payload. Its graph has the
occurrence of `A` one time. With the evidence of the merge that no two of its
occurrences are equal, the theorem of the other direction gives an order of
the merged diagram from the evidence of the word of its two runs. The link
gives each occurrence of the fourth source diagram its position in the graph
of the merged diagram, and the two calls of `A` have one position. One more diagram has
the effectful `C` between the two calls of `A`. The derivation of its merged
diagram has one interchange and the copy rule, and a check consumes its
soundness through a dependent payload that has the response of the store.

These parts are open:

- The soundness of the interchange rule for each interpretation in which each
  pure operation is central. The theorem of D2 is for each lowering in which
  each pure operation makes no call.
- The class of the operations that the copy rule, the merge of the equal
  calls, and the dependency graph read. The pure kind of a signature names an
  operation as central for the interchange rule, and it names the operation
  for copy naturality in these three places. An operation that is central
  only is not in the copy equation set.

## D4: the ready steps of a test with two cases

[Draft/Sequentialization.lean](Draft/Sequentialization.lean) has the list of
the ready steps of a test with two cases, when the rest of each case is a
diagram of the fragment with fixed occurrences. The list has the test. It
also has each step that is ready in the rest of the two cases, with one
operation and the same operands. The operands are ports of the context of the
test, and the test is pure or the step is pure. Such a step moves before the
test, and its element of the list has the diagram after it. A ready step of
the first case and a ready step of the second case give one element, so two
equal calls in one case give different elements.

The list is complete for the moves before the test. Each step that is ready
in the rest of each case, with operands of the context of the test, is in the
list, with a diagram after it that agrees at each case. The match of a ready
step with a call uses the decision of the identity of two operations, which
is a premise on the signature, and the decision of the identity of two ports.
[Draft/Diagram.lean](Draft/Diagram.lean) has the boundary with two cases and
the case analysis on them. [Prelude/Decision.lean](Prelude/Decision.lean) has
the decision of the identity of dependent pairs, the transport of a value
along a decision, and the law that the decision of the identity of an element
with itself gives the reflexivity.

[Draft/Checks/BinaryBranch.lean](Draft/Checks/BinaryBranch.lean) has the
checks, on Figure 5.6. The source diagram has a test, and each case has the
step `h` on the input `x`, the step `g` or `g′` on the output of `h`, and
the step `f`. It has seven steps. Its ready steps are the test and `h`. The
diagram with `h` at the front is from the list, and it has six steps. For the
evidence of the move of `h` that is not from the list, the theorem of the
completeness gives the position of `h` in the list. A check consumes the
agreement of the diagrams after `h` through a dependent payload, in each case
of the test.

The third diagram has `f` one time, as a continuation: each case exits to the
boundary of the continuation with its value. It has five steps. A derivation
in the control equation set relates the source diagram to the third diagram.
Its first part is the derivation of the ready step. Its second part has the
first exit equation and the composite equation, and the check gives that
part: no search finds the shared continuation. The two diagrams agree after
each lowering in which each pure operation returns without a call. The source
diagram calls the test before `h`, and the third diagram calls `h` before the
test, in each case of the test. The source diagram has a verified
implementation for a specification whose postcondition depends on the witness
of the precondition. The map of verified implementations along the derivation
gives the verified implementation of the third diagram. A check consumes its
evidence at the exit in each case of the test, for arbitrary functions of the
operations and an arbitrary witness.

A second group of checks has the operands of the ready steps. The test is
effectful, and its two cases have different numbers of ports. Each case has
two steps of one operation at one operand. For a pure operation and an
operand of the context of the test, the list has the test and the four pairs
of a step of the first case and a step of the second case. The list has the
test only in three conditions: the operands of the two cases are different
ports, the operand is an output port of the test in one case, or the
operation is effectful.

These parts are open: the search of a shared continuation, the coverage of
the sharing partitions, and the cost comparison of Figure 5.7.

## D6: generic definitions

[Prelude/Relation.lean](Prelude/Relation.lean) has the generic definitions of
D6, and [PreludeTests/Relation.lean](PreludeTests/Relation.lean) has their
kernel checks. These parts are complete: computations with graph, composition,
copairing, and agreement; the agreement of the graph of a function and then a
computation with that computation at the value of the function; the initial
property of the loop; the
correspondence of runs with paths; the fixpoint law, unrolling, and the loops
of two bodies that agree, each as an agreement; the domain evidence with its uniqueness and its construction from
a measure; the function with fuel with soundness and completeness; and the
transport of evidence that depends on a run across an agreement. Strength has
its two maps and one round trip. Naturality, uniformity for a function, and
the codiagonal have their two maps and no round trip. The two D6 checks for a
loop pass on these definitions. [Draft/Diagram.lean](Draft/Diagram.lean) has
the loop of the syntax with its function meaning. These parts are open: the
missing round trips, dinaturality, the laws of composition and of the control
sum for computations, the rules of the feedback equation set, and the source
constructions of the stage.

[Draft/Specification.lean](Draft/Specification.lean) and the modules under
[Draft/Specification](Draft/Specification) have the specification of a
diagram and the constructions on it, and
[Draft/Checks/Specification.lean](Draft/Checks/Specification.lean) has their
checks. The specification has two universe levels, which the specification of
the calls gives: the invariant of a loop has the level of the runs. The
runtime and the stop are at level 0. A specification of the calls with a runtime gives a specification of
a diagram. A response of a call is a response with the next runtime, or a
stop, and a result of a run is an exit with a runtime, or a stop. A witness of
the precondition of a diagram has a witness of the precondition of each call
that a run can make, and the runs of the diagram are over that witness. The
graph of a machine is a specification of the calls.

The Prelude part of these results is complete, with its kernel checks in the
Prelude tests.
[Prelude/Container/Verified.lean](Prelude/Container/Verified.lean) has the
runs of a computation along its evidence, and the condition at the result of
each run. It has the specification of an implementation from the
specification of its calls: the implementation is verified for it, and each
specification with a lift of the implementation maps to it.
[Prelude/Container/Runtime.lean](Prelude/Container/Runtime.lean) has the unit
runtime. [Prelude/Identity.lean](Prelude/Identity.lean) has the law for a
family on the identities from one element, and the sum over an isomorphism of
the bases. [Prelude/Relation.lean](Prelude/Relation.lean) has the agreement
of the loops of two bodies that agree.

The precondition of a loop is an invariant: a family on the entrances that the
body keeps, with a witness of the precondition of the body at each entrance of
the family. The runs of the loop are the loop of
[Prelude/Relation.lean](Prelude/Relation.lean) on the entrances with the
family, so a loop that does not stop has a witness and no run. One iteration
of a loop has the runs of the body at the result that the next entrance, the
exit, or the stop names.

The two exit equations hold for the specification. A witness for an exit to
the boundary of a continuation, and then the continuation, gives a witness
for the continuation at the case of the exit, and the converse. One composite
of the two maps is the identity by computation. Over each witness, the runs
of the composite are the runs of the continuation, as an equivalence with its
two round trips. The runs of an exit past a continuation, and then the
continuation, are the runs of that exit, as an equivalence with its two round
trips. Each equivalence is one application of a law of
[Prelude/Identity.lean](Prelude/Identity.lean): a family on the identities
from one element is its value at the reflexivity. The runs of a loop over a
witness are the loop of its iterations, by computation. The checks on the
countdown loop have the first exit equation at the run of the whole diagram,
with its round trip, and the unrolling law and the fixpoint law at the run
from the counter 2, with their round trips.

The function meaning and the specification of a diagram are two recursions on
the diagram, and their connection has two halves. A witness of the
precondition of a diagram gives the evidence of the computation of the diagram
with each number of unrollings, for evidence of the rest at each result of a
run. The second
half is the completeness: a run of the diagram, and then a run of the rest, is
a run of the computation along its evidence, from a threshold of the number of
unrollings.

A verified diagram, for a specification of its interface with a runtime, is a
map into the specification of the diagram: a witness of the precondition of
the diagram, and the postcondition at the result of each run over that
witness. A bound is second evidence: each run over the witness reaches the
limit of a loop only at a runtime with a given condition. A witness with its
bound gives the evidence of the approximant, for a computation at the limit
that has evidence at each runtime with the condition. With the empty
condition, it needs no evidence for the computation at the limit, and this
real bound is the route to a verified implementation of an approximant. With
a condition that each runtime has, the computation at the limit needs
evidence of the postcondition from each runtime. For a postcondition that
fixes the last runtime, such as the postcondition of the countdown, no
computation has that evidence, because the runtime of the machine only
grows.

A specification of the calls with no runtime is the case of the unit runtime
with no stop: the specification with that runtime has the precondition of the
call, and the postcondition of the call at each response. The two keep their
universe levels. The evidence of a computation and the evidence of the
computation with the unit runtime give each other. The evidence of a diagram
at the unit runtime gives the verified implementation of each approximant
with no runtime. Its condition at the limit is one type, and its constructor
of a loop has the family with a count.

A cartesian map of specifications gives a witness of the second precondition
from a witness of the first, and an equivalence of the runs over the second
witness and the runs over the first, with its two round trips. A rule set
holds for a specification of the calls when each rule has a cartesian map
between the specifications of its two sides, in each direction. A derivation
in such a rule set has these maps, by a recursion on the derivation, and a
verified diagram moves along them. In a composite and in a frame, the witness
of the later part depends on the run of the first part. In an iteration of a
loop, the invariant at the next entrance depends on the run of the body. The
equivalence of the runs is thus a sum over an equivalence of the runs of the
first part. That sum needs the two round trips of the
first equivalence to agree, and an isomorphism has a first round trip with
that property. The equivalence of the runs of a loop is one application of
the agreement of the loops of two bodies that agree. The two laws are in
[Prelude/Identity.lean](Prelude/Identity.lean) and
[Prelude/Relation.lean](Prelude/Relation.lean). The checks on the countdown
loop have the two maps of the equivalence at a run, and its two round
trips. These checks have a derivation from a loop to the same loop, with no
rule. The second exit equation is a rule with a cartesian map in each
direction, for each specification of the calls. One more check has that rule
under a step, a copairing, and a loop, between two different loops: a loop
whose exit is an exit past a continuation, and then that continuation, and
the countdown loop. It has the two maps and the two round trips at a run.

The specification of a diagram with a bound has the witness of the diagram
with its bound as the witness of its precondition, and the runs of the
diagram. The evidence of a diagram at an input, for a condition at each result
of a run, is the evidence of one call of that specification, in the form of
the Prelude. The evidence at each input with a witness of a specification of
the interface gives the verified implementation of the approximant. The
constructors of this evidence have the forms of a diagram. An exit has its
condition. A step has a witness of the precondition of its call, the
condition at each stop, and the evidence of the diagram of each response. A
composite and a frame have a condition at the boundary of the later part. A
loop has an invariant at its entrance, which the body establishes at each
exit to the entrance, and which gives the condition at the limit.

A second constructor of a loop has a family on the entrances with a count:
the number of the unrollings that are sufficient. The body goes from the
family at one more to the family at the next entrance, no entrance has the
family at zero, and the entrance has the family at the number of unrollings.
The invariant is the family with its count, and the count at the next
entrance is one less by computation. With the empty condition at the limit,
this evidence gives the verified implementation of the approximant with no
evidence for the computation at the limit. The checks have the countdown for
each counter that is less than the number of unrollings, and a loop in a
loop, where one number of unrollings is for the two loops.

The map that forgets the bound gives the verified diagram, which moves along
a derivation. For a condition at the limit that each runtime has, each
witness of the precondition of a diagram has the bound, so evidence that
moved is again a part under a constructor. A check moves the evidence of a
loop with no count along a derivation with the second exit equation under the
loop, and it consumes the moved evidence at a run of the second diagram over
the moved witness.

The verified implementation of an approximant moves along a derivation in a
rule set that holds in a congruence. The approximants of the two diagrams
agree at each number of unrollings, and the verified implementation moves
along that agreement with its specification. Thus the result of a real bound
moves along a derivation, and no constructor gives the evidence of the second
diagram. Two checks move the verified countdown with a count along a
derivation with the interchange rule under the loop, with the same number of
unrollings. The second diagram has the effectful step before the pure step in
each iteration, so the two diagrams make different calls. One check moves the
evidence of the machine of the diagram: the interchange rule holds on the
machine of the calls, because that machine is the machine of the lowering on
a machine of the store. The second check moves the verified implementation
with no runtime, after the lowering. The witness with its bound does not move
in this manner. The verified implementation of the whole diagram moves in its
place, because a derivation of a part gives a derivation of the whole. This
map needs a rule set that holds in a congruence, and the two approximants at
one number of unrollings.

The peel of a loop is a map of specifications from the loop to one copy of
the body, and then the loop. A witness of the loop gives a witness of the
second continuation, and a run of the second continuation gives a run of the
loop, whose first iteration is the run of the copy. It is a map in one
direction, and the evidence of a loop moves along it: a check consumes it at
a run of the peeled diagram. At one number of
unrollings, the approximants of the loop and of the peeled diagram are
different computations, so the peel is not an agreement of the approximants.
With a real bound, the constructors give the evidence of the peeled diagram,
and one unrolling less is sufficient.

These parts are open:

- A loop with a count whose limit a run reaches. The loop constructor with a
  count has no entrance at the count zero: a witness of the precondition of a
  loop has a witness for the body at each entrance that a run reaches.
- A real bound along the peel, and along each map that is not an agreement of
  the approximants at one number of unrollings. The constructors give the
  evidence of the peeled diagram again. The evidence with no bound moves
  along the peel, and for the countdown it gives no verified implementation
  of an approximant.
- The peel as a rule of a derivation, with a cartesian map in each direction.
  The direction from the peeled continuation to the loop needs one invariant
  from the invariants after each run of the copy, and an equivalence of loops
  over different families of entrances.
- The cartesian maps for each rule set of D2 and D3, with the condition on
  the specification of the calls. The obligation of a rule is an equivalence
  of the runs, so the condition is stronger than the condition for a map in
  each direction. The copy rule and the interchange rule are the first cases:
  the copy rule relates one response of a pure operation, with its evidence,
  to two, and the interchange rule relates the runs of the two orders.
- The round trip at a run over the moved witness, for a derivation with two
  loop forms. Its check by `.refl` is above the default limit of the
  elaborator, and the kernel accepts the same term. The cause is the proof
  that the two round trips of an isomorphism agree: the elaborator evaluates
  it again at each iteration, and the composite of two equivalences gives it
  a run that is not in normal form. The check passes for a derivation with
  one loop form.
- The least threshold of a run.
- The two round trips of the connection for each diagram.

## D7: the frontend fragment

[Draft/Stele.lean](Draft/Stele.lean) has a typed fragment of Stele. The types
are integers with no bound, and booleans. An expression has a context of
local variables, and a variable is a position of the context. The constructs
are literals, variables, a read of a storage variable, the arithmetic and
comparison operations, negation, Euclidean division and remainder, the
reduction of an integer to a number of bits, `&&`, `||`, the conditional
expression, a declaration, an assignment to a local variable or to a storage
variable, `require`, `if`, `while`, and `return`. A storage variable is a slot
number.

The signature has one operation for each construct that computes. A read and
a write of storage are effectful. `revert` is effectful and has no output
case. Division and remainder are pure, and their output boundary has a case
for a zero divisor. The translation is a recursion on the syntax. A table has
the port of the present value of each local variable, and an assignment
changes the table only. `&&`, `||`, and the conditional expression evaluate
one of two expressions, as in Stele: the two paths of a test exit to one case
of the boundary of a continuation. The two paths of an `if` exit to one case
of the boundary of a continuation, with the present value of each variable at
its ports. A `while` is a loop whose entrance has the variables. The module
has the machine of the operations, with the storage as its runtime.

[Draft/Checks/Stele.lean](Draft/Checks/Stele.lean) has kernel checks of
compiled programs of the fragment: a declaration with a write and a read of
storage, for arbitrary arguments and an arbitrary storage; an `if` with an
assignment in one path; a `while` with two assignments; a `while` that writes
storage, for an arbitrary storage; a `require` and a division that stop at a
zero divisor; and `&&`, `||`, and the conditional expression at a zero
divisor.

The library `Frontend` imports EquiVM, so it is outside `Draft`.
[Frontend/Stele.lean](Frontend/Stele.lean) has the translation from the Stele
syntax of EquiVM to the typed fragment. It resolves each name to a position
or to a slot, and it checks each type. The value of the call is a variable
with no name at the first position of the context of a function. A write of
a storage variable reduces the value to the bits of the variable. The
translation rejects a declaration of a name that is in scope, because the
locals of Stele are one map for a function and the fragment ends the scope of
a declaration with its block. A rejection has a reason as data. The
translation depends on no axiom.

[Frontend/Checks/Stele.lean](Frontend/Checks/Stele.lean) has a contract in
the notation of EquiVM, and compiled observations of the runs of its
translated transitions.
[Frontend/Checks/Agreement.lean](Frontend/Checks/Agreement.lean) runs each
transition two times, from one value of the call, one list of arguments, and
one storage: the diagram of the translated function, and the body by the
executable semantics of EquiVM with the Solidity layout of the storage. The
two observations are equal for each of the 16 cases.

These parts are open:

- The correspondence of the fragment: a semantics of the typed fragment, and
  the proof that the run of the diagram of each program has the result of
  that semantics. It is a part of the implementation.
- The correspondence of the translation: the relation between the semantics
  of Stele in EquiVM and the semantics of the typed fragment, for each
  program that the translation accepts. It is an observational proof.
- The other constructs of Stele: `for`, `break`, `continue`, the signed
  storage types, the range check of a cast, the other value types, mappings
  and arrays, calls, and the other values of the environment.
- A function with no returned value, or with more than one.
- The correspondence of the fragment has Aberlé's form: the semantics of the
  fragment is a specification of the interface with a runtime, and the
  diagram of each program is a verified implementation of it, with the graph
  of the machine of the operations as the assumption on each call.
- The backend.

## Research scope after the bounded milestones

The full scope includes faithful VSDG translation, admissible implementation
choices, effect-sensitive transformations, failure/divergence observations,
feedback, and lowering. Finite pure source examples establish a
bounded milestone; they do not replace those broader obligations.
