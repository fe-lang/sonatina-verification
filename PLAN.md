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
| `Prelude.Container` and its submodules | Shared polynomial interfaces, lenses, sums, products, families, reindexing, one-call dependent evidence, `Free` computations, implementations, and their structural laws |
| `Prelude.Container.Section`, `Prelude.Container.Verified` | Shared `DepPoly`, `FreeDep`, verified implementations and composition |
| `Draft.Implementation` | Compiler operation interfaces with their specifications, and their verified implementations |
| `Draft.Diagram` | The one diagram syntax: signatures of pure and effectful operations, contexts and boundaries with their structural maps, diagrams with exits, steps, and composites, continuations with copairings, frames, and loops, the function meaning and the run family, the derivation rules of each equation set, bypasses, resolution, substitution, the laws of the loop, and structural cells and execution certificates |
| `Draft.Verified` | The verification over the diagram syntax: the interface of a diagram, the evidence of a diagram by its constructors, the lift for a specification, the verified implementation, and the map of verified implementations along a derivation |
| `Draft.Runtime` | The runner of that syntax: the interpretation of effects with the runtime, state equations, invariant evidence, and dependent rewrite maps |
| `Draft.Source` | Source diagrams as presentations of a VSDG, the relation between two presentations, the frontend interface, sharing, control, and feedback translation, and admissibility evidence |
| `Draft.Sequentialization` | The selection of a realization by cost, certified realizations, coverage, and soundness |
| `Draft.Lowering` | The backend interface, placement and storage obligations, the Stele and EVM adapters, and target refinement |
| `Draft.Checks` | Named kernel consumers and functional checks |
| `Observations` | Observational proofs of correctness for metatheoretical verification. They can use axioms, and no implementation module depends on them. |

The Prelude identity, indexed, decision, relation, and container modules,
`Draft.Diagram`, `Draft.Verified`, and `Draft.Checks` exist. The other module families are the
planned locations for stages D2 to D7. The module families divide the work
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
| D2. Whole diagrams with effects | Signatures of pure and effectful operations, with input ports and an output boundary for each operation. Contexts, boundaries as lists of contexts, and their structural maps: copy, discard, and exchange on ports, and the join on cases. Diagrams: exits, steps, and composites. Continuations: copairings, frames with a bypass, and loops. The static size of a diagram. The structural agreement of two diagrams whose families agree at each case, with its soundness. The request interface of a signature at a family of values, with the specification of each operation as a part of the signature. The function meaning of a diagram into `Free`, with the remaining computation as an argument, for a number of unrollings of each loop and a computation for the limit. The verification of a diagram over its function meaning, in `FreeDep`, by the constructors of the diagram: a step takes the witness of the precondition of its operation from the context, and its continuation receives the postcondition of the response. The run family of a diagram, for the calls with a runtime: a recursion into the relations of `Prelude.Relation`, with its two exit equations as equivalences. Each law of the stage is an agreement of function meanings for each number of unrollings, and the evidence of a verified diagram moves along it. The interchange rule for a pure step and a step that no wire connects to it, with its agreement for each lowering in which each pure operation makes no call, and with the map of verified diagrams along that agreement. The state runner, with whiskering and pure centrality. The control equation set for the state runner: the two case equations, the pointwise uniqueness of a map out of a sum, preservation by whiskering, the agreement of a composite with the diagram that has the continuation at each exit, and the agreement of a frame with the copairing that has a copy of its diagram for each case of the bypass. Branching read/write with a shared invariant, and the applicable global-state rewrite evidence. Each law is a pointwise statement, so that the graph of a function carries it to the relations of D6. The D2 checks below pass. | Current |
| D3. Dependency orders | Source diagrams for the fixed-occurrence fragment: one sequence of steps and one exit. The dependency graph of a diagram: its steps with their operand ports, and the order of its effectful steps. Each dependency-respecting order is a diagram of the same syntax with an interchange derivation from the source diagram, and its context at each step has the cut of live values. The evidence of each order is constructed from the evidence of the source along the derivation, with the condition on the specifications of the pure operations that the construction needs. Soundness for the interchange equation set: actual producer connections, exact call order, and returned-value preservation. Constructive coverage that returns a realization with its derivation for an arbitrary admissible order. The three interleavings and the shared, repeated, and discarded operand checks pass. | Pending |
| D4. Control and sharing | Source diagrams with the control sum: tests as steps with one diagram for each case, copairing for values and for the runtime, joins as two exits to one case, composites for shared continuations, and guarded operations. The relation between two presentations of one VSDG, for the order of two pure tests that no wire connects and for the case of an operation. Occurrence partitions. Figure 5.6 and the five arrangements of Figure 5.7, each as a whole diagram. Retained bypass cases are related to source control information. Tail sharing is justified with the control equation set. Reuse and speculation are justified with the copy and discard equation sets, the applicable effect equations, and dependent evidence maps. Position invariance holds for each operation that is named for discard naturality, and a guarded operation consumes the port of its case. The two sharing hypotheses of CONCEPT are tested. Soundness and coverage hold for the claimed fragment. Costs are compared under the register-machine model of the thesis, which gives the instruction counts of the source contracts. | Pending |
| D5. Substitution and composition laws | Exact silent resolution with closed cycles. Substitution with multiplied bypasses, and substitution closure. Identity and associativity with reindexing. Adequacy of finite routing certificates. Interpretation, runtime, and dependent verification commute with nested substitution. | Pending |
| D6. Feedback | Computations as Type-valued relations, with the graph of a function, composition, the control sum, and agreement as an equivalence of run families. The loop of a body as the inductive family of runs, with the initial property: the map to each relation that the body closes, and its uniqueness at each run. For a function body: the function on the inductive domain, the uniqueness of the domain evidence, the function with fuel with soundness and completeness against the runs, and domain evidence from a decreasing measure. The consequences of the initial property, each as an equivalence with its two round-trip identities: fixpoint, naturality, codiagonal, dinaturality, uniformity for pure maps, and preservation by whiskering. The transport of a postcondition that depends on the run across each law. The generic definitions extend `Prelude.Relation`. The loop of the syntax: the laws of the run family of a diagram from the laws of composition and of the control sum for computations, and the soundness and the completeness of the function meaning against the runs, for a function of the calls. The rules of the feedback equation set, with their soundness as equivalences of run families. The trace as a derived operation of the loop, with the trace laws as consequences. The compatibility of a bypass with the loop, the agreement of staged execution with all-at-once execution, and cell pasting from uniformity, for the declared observation. Source loop initialization, carried values and state, guards, and exits. Invariant-preserving iteration with the domain evidence as the precondition witness. Correspondence with traced wiring and execution certificates. Feedback compatibility for a changing runtime and a preserved bypass context. The derivation of each loop choice of thesis §5.4 that the stage covers, and a statement of the work that infinite control and infinite observations still need. | Pending |
| D7. Example pipeline slice | The frontend and backend interfaces of CONCEPT, with Stele and the EVM as the instance. A source-to-target slice with compositional proof production, placement and storage accounting, and constructive Stele/EVM adapters. The declared value, effect, termination, and choice observations are preserved. The backend interpretation satisfies the named equation sets under its agreement relation. The direction from target runs to source runs gives the refinement relation of EquiVM at the boundary. The direction from source runs to target runs holds above a gas bound that exists for each source run. The lowering causes no stack underflow, no stack overflow, and no bad jump destination. The cost account uses the stack machine of EVMLean: gas for each instruction, code size, the reach of `DUP` and `SWAP`, the stack limit, and equal stack layouts at each merge. | Pending |

The laws of D2 are the laws of the equation sets without feedback, and they
hold for a diagram with a loop for each number of unrollings. The source
fragments of D3 and D4 have no loop. Each realization is written
as one whole diagram, so these stages need no substitution law. D5 supplies
substitution and its laws for the stages that nest diagrams. D6 has the one
feedback structure: the loop with its laws, and the trace as a derived
operation. D5 and D6 address different termination questions.

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
construction for each diagram, and for a specification that does not fix the
response, is open for D2 and D3.

[N6](NOTES.md#n6-slow-elaboration-is-not-slow-kernel-checking) has the three
results on cost that the checks gave: the effect of `smartUnfolding`, the cost
of a generated matcher on an indexed family, and the cost of a sequence that
binds its earlier part.

## D2: current

[Draft/Diagram.lean](Draft/Diagram.lean) has the plain part of each
construction. [Draft/Verified.lean](Draft/Verified.lean) has the verification
over it, by the method of [CONCEPT.md](CONCEPT.md#design):

- The interface of a diagram, and the diagram as an implementation of that
  interface by calls of the interface of its signature.
- The evidence of a diagram at the values of its context, for a postcondition
  at each exit. It is the dependent form of the function meaning: it has the
  evidence of the remaining computation as an argument, and the evidence of
  the computation at the limit of a loop. Each constructor of a diagram and
  of a continuation has its evidence. A step takes a witness of the
  precondition of its operation, and the diagram of each response receives
  the postcondition. A composite has a condition at the boundary of its
  continuation, a frame has a condition at the exit of its diagram, and a loop
  has an invariant.
- The lift of a diagram for a specification, which is a `DepPoly` on the
  interface of the diagram, and the verified implementation (`ImplDep`) that
  the lift gives. The composition with a verified lowering is `ImplDep.trans`.
- The map of verified implementations along a derivation, for a rule set that
  holds in the lowering.

The specification of the operations is a `DepPoly` on the request interface
of the signature. [Draft/Checks/Lift.lean](Draft/Checks/Lift.lean) has four
verified diagrams, each with a verified lowering and kernel checks that
eliminate the evidence at the exit: the two orders of a pure step and an
effectful step, with the lift of the first order moved to the second order
along the interchange derivation; one continuation of two control paths,
with a condition on the sum that each path establishes from the postcondition
of the test; one effectful step of two control paths in a frame; and the loop
that counts down, with an invariant that has the receipts of the calls and
the identity of the value. Three plain parts of the module are open:

- An implementation that returns without a call is a verified implementation
  against the specification that admits no call. The two forms become one.
- The form of the calls with a runtime: a relation of calls, or a machine
  that has the runtime as its state.
- The form of the frame, which is a part of the work on the wiring.

The text below describes the plain part.

[Draft/Diagram.lean](Draft/Diagram.lean) has the signatures, the boundaries
as lists of contexts with their product, the port maps, the diagrams, the
continuations with the loop, the static size, the function meaning into
`Free`, and the run family.
The function meaning has a number of unrollings and a computation at the limit
of a loop. A loop with no unrolling is that computation, and a loop with one
more unrolling is its body with the loop at each exit to the entrance, by
computation. Each law of the module is a law for each number and each
computation at the limit, and its case for the loop is an induction on the
number. The run family is a recursion into the relations of
[Prelude/Relation.lean](Prelude/Relation.lean), for a relation of calls with a
runtime. An exit is the graph of its function, a composite is the composition
of relations, and the runs of a loop are the loop of that module for the
iterations of its body. Its two exit equations are equivalences with their
two round trips: each is the law of that module for the graph of a function
and then a computation.
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
composite of two maps have that law for the computation. A map of exits
acts on the exits of a diagram, and a family with a diagram for each exit
case gives the diagram with those diagrams at its exits. Each of the two has
its law for the computation. The derivations of a
rule set are the smallest relation that has the rules and structural
agreement, and that is an equivalence and a congruence for each form of a
diagram and of a continuation. One theorem gives the soundness of each rule
set: an implementation in which each rule holds gives computations that agree
for each derivation. The interchange rule relates the two orders of two steps
that no wire connects, of which one is pure. It holds in each implementation
in which each pure operation returns without a call. The two exit equations
of the control sum are rules too. An exit to the boundary of a copairing, and
then the copairing, is the diagram of the case of the exit, with renamed
ports. An exit past a continuation, and then the continuation, is that exit.
[Prelude/Indexed.lean](Prelude/Indexed.lean) has the positions of a
concatenation, the case analysis of a position of a nonempty list, and the
selection of values at a list of positions, with their laws. [Prelude/Container/Free.lean](Prelude/Container/Free.lean) has the
implementation of a shape that returns without a call.

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
  three laws of renaming for the computation.
- A pure operation and two effectful operations. Two interchanges move the
  pure step after the two effectful steps: one at the first step, and one
  after the first effectful step, by the congruence of a step. The symmetry
  of the relation moves it back. The check of the soundness has closed
  inputs, and only the kernel reduces it.
- A test with a different sum in each case, one exit case for the two paths,
  and one effectful continuation. The composite and the diagram with the
  continuation at each exit give the same values in each case of the test.
  The check consumes the identity that the agreement gives. The composite has
  4 steps, and the diagram with the continuation at each exit has 5.
- A test, one effectful step for the two paths, and a different sum after
  that step on each path. A frame has the one copy of the step, and its
  bypass keeps the path and one input. After the substitution, the frame and
  the diagram with a copy of the step in each path are one computation with
  one call, in each case of the test. The frame has 4 steps, and the diagram
  with a copy of the step in each path has 5.
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

These parts of the stage are open: the identity law and the composition law
of the action of a port map as structural agreements of diagrams, the
agreement of each frame with the copairing of its copies as a rule, the
state runner with an arbitrary runtime and its invariant, the uniqueness of a
map out of a sum, and the read/write evidence. The stage continues with one row
of its table at a time.

## D6: generic definitions

[Prelude/Relation.lean](Prelude/Relation.lean) has the generic definitions of
D6, and [PreludeTests/Relation.lean](PreludeTests/Relation.lean) has their
kernel checks. These parts are complete: computations with graph, composition,
copairing, and agreement; the agreement of the graph of a function and then a
computation with that computation at the value of the function; the initial
property of the loop; the
correspondence of runs with paths; the fixpoint law and unrolling, each as an
agreement; the domain evidence with its uniqueness and its construction from
a measure; the function with fuel with soundness and completeness; and the
transport of evidence that depends on a run across an agreement. Strength has
its two maps and one round trip. Naturality, uniformity for a function, and
the codiagonal have their two maps and no round trip. The two D6 checks for a
loop pass on these definitions. [Draft/Diagram.lean](Draft/Diagram.lean) has
the loop of the syntax with its two meanings. These parts are open: the
missing round trips, dinaturality, the laws of composition and of the control
sum for computations, the laws of the loop of the syntax, and the source
constructions of the stage. The laws of the loop of the syntax are the laws
of the run family of a composite and of a copairing, the soundness and the
completeness of the function meaning against the runs, and the rules of the
feedback equation set.

## Research scope after the bounded milestones

The full scope includes faithful VSDG translation, admissible implementation
choices, effect-sensitive transformations, failure/divergence observations,
feedback, and lowering. Finite pure source examples establish a
bounded milestone; they do not replace those broader obligations.
