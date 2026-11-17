# Sonatina: polynomial foundations for compilation

[Premises and scope](#premises-and-scope) fixes the premises of the
investigation and is immutable during implementation. [Design](#design) gives
the source correspondences, the specification of admissible realizations, and
the representation decisions that implement those premises.
[NOTES.md](NOTES.md) gives the research observations and the source contracts.
[PLAN.md](PLAN.md) defines the stages and tracks their status.
[docs/API.md](docs/API.md) describes implemented interfaces.

## Premises and scope

Sonatina investigates a compiler design whose intermediate representation is
constituted by polynomial interfaces, string diagrams, and their algebraic
structure. The project reappraises Value State Dependence Graphs (VSDGs) from
first principles, taking `Int(Poly_*)` and the premonoidal string-diagrammatic
calculus as its mathematical foundations. VSDG supplies the computational
phenomena, dependencies, and compilation problems to be articulated in this
setting. The central research problem is sequentialization: understanding how
a program's dependencies, sharing, control alternatives, and effects admit
sequential implementations, and how transformations change the available
implementations.

The IR's representations, operations, and implementation interfaces must be
derived from the categorical construction. Each foundational definition must
identify the mathematical objects, morphisms, composition, and laws it
represents. The relationship between dependency structure and admissible
sequential realizations is part of that construction.

[Lawrence's thesis](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-705.pdf)
provides the principal account of these difficulties. VSDG's carefully developed
architecture and practical success provide substantive guidance. The research
method is to seek a faithful translation of VSDG within the categorical
frameworks, using its dependency structure, sharing semantics, and admissible
realizations as the reference. The precise preservation statements must emerge
from that translation effort and be justified against the source account.

Departures from VSDG require a high burden of proof: a concrete benefit, a
reason that the departure is warranted, and evidence that it preserves the
soundness of the architecture and design. Proposals for such departures must
arise from productive opportunities encountered in the actual refoundation.
The faithful translation supplies the basis for assessing their meaning and
consequences.

The working hypothesis is that VSDG's bespoke formalism limits its development,
and that the supplied categorical frameworks contain the structure required
for a principled compiler architecture that is a spiritual successor to VSDG.
The mathematical innovation is the faithful integration of the premonoidal
string-diagrammatic calculus with the polynomial frameworks. Compiler
structures and their laws are to be developed within these foundations;
extending the foundations is outside the scope of the investigation. Their
sufficiency is a hypothesis to test through the construction.

A categorical reformulation can make VSDG's underlying structure explicit,
clarify the conditions under which Lawrence's techniques apply, and expose
further transformations or sequentialization methods. The value of the
reformulation depends on what it explains about these problems: which sharing
arrangements admit sequential realization, what information those realizations
must retain, and which structural or effect equations justify transformations. These
questions give the categorical construction a concrete criterion of usefulness.

The organizing structures of the IR are typed open diagrams and polynomial
boundaries. Interfaces, operation signatures, regions, wiring, sharing, and
feedback each require an account within this framework. Diagrams compose by
substitution into open boxes, with identities, associativity, and the relevant
coherence laws. A representation of a VSDG fragment should translate its
dependencies and observable behavior into this calculus. Sequential evaluators,
control-flow graphs, and machine code provide interpretations and concrete
realizations of diagrams.

The work of [Kondyrev–Spivak](https://arxiv.org/abs/2509.05462)
provides the polynomial control-flow foundation: polynomial boundaries,
control regions containing data ports, and an operad of wiring diagrams based
on `Int(Poly_*)`. Trace on `Poly_*` supplies feedback; algebras of the wiring
operad describe the computations filling boxes; and the double-categorical
and operational structures relate diagrams to trajectories. Multivariate and
labelled versions provide resources for typing data and expressing data
transformations. The relationship between these constructions and a compiler
IR is a mathematical construction to establish.

An open diagram with inner boxes `P₁, …, Pₙ` and outer box `Q` is a whole wiring
morphism in `W(P₁, …, Pₙ; Q) = Int(Poly_*)(P₁ + … + Pₙ, Q)`. Each box has
polynomial input and output boundaries. The paper's `Para_×` construction
supplies bypassing: with bypass polynomials `Mᵢ`, the underlying routing has the
form

```text
Q.input + Σᵢ (Mᵢ × Pᵢ.output)
    → Q.output + Σᵢ (Mᵢ × Pᵢ.input) + 1
```

Here `Σᵢ` denotes polynomial coproduct, `×` the polynomial product retaining
context around a box, and `1` the undefined alternative. Routing among inner
boxes, feedback, and substitution of whole diagrams are foundational
operations. Their interpretation must account for partiality and
nontermination. Computational meanings are supplied by algebras of the wiring
operad; the correspondence between diagram substitution and semantic
composition must be established.

The resemblance between VSDG structure and linear logic motivates explicit
structural rules. Reusable values should carry comultiplication
`Δ_X : X → X ⊗ X` and a counit `ε_X : X → I`, expressing copying and discarding.
These require coassociativity, counit laws, and commutativity where appropriate,
along with compatibility laws for the permitted computations. The choice of
tensor and the scope of each law must be explicit. Data copying inside a
control region, control branching, polynomial substitution, and composition
of program regions have distinct roles that require their own definitions
and relationships.

State dependencies can occur in multiple static alternatives while their uses
remain dynamically linear. A categorical account must express how alternatives
share access to a resource, how selection and reconvergence preserve that
resource, and when simultaneous uses are permitted. This includes the
interaction between reusable values, state-dependent observations, and effect
ordering. Structural restrictions need both semantic justification and closure
under diagram composition.

The work of [Román–Sobociński](https://arxiv.org/abs/2305.06075)
provides the foundation for effects through premonoidal and effectful
categories and string diagrams with an explicit runtime object. Their
global-state example combines value comonoids with read/write operations and
equations relating them, including a comonoid coaction on the runtime. Such
algebraic structure is a language for investigating the VSDG's value/state
distinction. The admissible interactions of pure and effectful computations,
including their ordering and sharing laws, must be specified within this
calculus. The precise relationship between it and the polynomial control-flow
calculus is part of Sonatina's investigation.

Trace on `Poly_*` is the proposed basis for a categorical account of μ-binding
loops. The correspondence must relate a loop's boundary, initialization,
carried values and state, guard, and exits to a traced diagram. Uniformity and
trace laws are candidate tools for reasoning about changes of loop
representation, cuts, and unrolling. Establishing their application to VSDG
loops is a research obligation, including an explicit treatment of partiality
and nontermination. Pipelining introduces further obligations concerning
overlapping iterations and effects.

Verification belongs to the same compositional organization.
[Aberlé's framework](https://arxiv.org/abs/2604.01303)
uses polynomials as interfaces, free-monad constructions for implementations,
dependent polynomials for pre/postcondition specifications, and stateful runners
for operational interpretations. This offers a route to contracts whose proofs
compose with implementations. How such contracts attach to Sonatina's regions
and transformations is part of the investigation. Their specifications must
account for retained information, value provenance, resource use, and invariants
across feedback.
The Lean formalization uses Type-valued evidence where proofs form part of
these constructions.

The polynomial and effectful calculi have distinct semantic roles.
Their combination requires explicit translations and compatibility
theorems between control wiring, the algebra of effects, and dependent
specifications. Its foundations must identify which equations hold
structurally, which require properties of a primitive operation, and which
depend on the chosen observational semantics.

Within this setting, sequentialization can be studied as the construction of
admissible realizations or factorizations of a diagram. The questions include
which control distinctions a boundary must retain, where values must remain
available, how reuse and tail sharing interact, and when duplication,
speculation, or additional storage preserves behavior. The faithful translation
must account for the implementation choices left open by the dependencies of
the translated VSDG fragment. The form and strength of that correspondence are
to be established through the translation itself. Any restriction of those
choices is a departure subject to the same benefit and soundness requirements. A particular traversal,
storage layout, or routing mechanism is an additional choice whose correctness
must be established.

The observation contract must be grounded in the faithful translation and its
concrete semantic obligations. The treatment of termination, divergence,
failure, returned values, state, and effects must be investigated where those
phenomena occur in the source and its categorical interpretation. The
undefined alternative in a polynomial interface does not by itself determine
which of these distinctions the compiler's correctness relation preserves.
Each preservation theorem must state its observations and assumptions once
that correspondence is understood.

Semantic preservation and implementation cost require separate accounts.
Two realizations can agree on observable results while differing in code size,
retained storage, predicate evaluations, or speculative work. Conversely,
resource conservation and agreement on a final store can coexist with different
returned values. The semantic equations of an effect theory determine which
operations can be identified; traces and cost annotations record additional
information under an explicitly chosen interpretation.

Lawrence's examples, especially Figures 5.6 and 5.7, are concrete tests of the
framework. VSDG's native results and their original realization constraints
provide regression baselines. The investigation also explores the opportunities
that the richer mathematical setting exposes, including new sharing
arrangements, retained information, control tests, duplication, and speculation.
Each comparison must make its constraints and costs explicit, preserve the
baseline result under its original assumptions, and justify any claimed
improvement by the benefit and soundness requirements.

Experiments must instantiate the framework's polynomial objects and
diagrammatic constructions, express the competing sharing arrangements, and
establish what permits or obstructs their realization. Their purpose is to
develop a practical compiler IR architecture, drawing on VSDG's established
strengths and overcoming its limitations wherever the evidence warrants it.
The principal obligations are:

1. A typed foundation derived from `Int(Poly_*)` and its wiring operad, including
   whole-diagram substitution, bypassing, feedback, and their laws.
2. An explicit relationship to the premonoidal effect calculus, accounting for
   value comonoids, runtime structure, and admissible effect equations.
3. A translation of VSDG dependencies into this setting that specifies the
   information, behavior, and implementation choices preserved.
4. Transformations and factorizations justified within the calculus, together
   with semantic preservation and conditions on effects.
5. An analysis of sequential realizations that makes retained information,
   control decisions, and costs explicit.

Operational models and concrete implementations require correspondence
theorems with the diagrammatic construction. These theorems specify the
observations preserved and the assumptions on effects and resources. Each
experiment must identify the construction and property it tests, the
assumptions of its proofs, and what its result establishes about
sequentialization.

Sonatina is a general IR. Each frontend and each backend supplies its
language, its semantics, and its arithmetic, failure, and resource
assumptions. The example pipeline is `Stele → Sonatina polynomial IR → EVM
bytecode`. EquiVM supplies Stele facilities, and EVMLean supplies the target
language and semantics. Frontend translation, IR optimization, sequential
realization, and lowering each require their own preservation statements,
composed under explicit assumptions about effects and observable behavior.
Arithmetic, failure behavior, and resource assumptions must be explicit at
the source and target boundaries. The distinction between semantic
preservation and resource cost also applies when the program can observe its
available resources.

## Design

The IR is one syntax of string diagrams. A diagram has operations, value
wires with copy and discard, one runtime wire, and the control sum. The
premonoidal calculus gives the laws of the syntax: a pure operation is
central, and the effectful operations keep their order on the runtime wire.
Polynomials formalize the syntax: a boundary is a sum of control cases with a
product of typed ports in each case, and the wiring of `Int(Poly_*)` gives
composition, substitution, retained context, and feedback. The two frameworks
are not two layers. They describe the same diagrams, and the premises name
their integration as the innovation of the project.

A diagram goes from a context to its exits. A context is a product of typed
ports, and a boundary is a finite sum of contexts. The exits are a list of
boundaries: the boundary of the nearest continuation is first, and the exits
around that continuation follow. A whole diagram has one boundary, which is
its exit boundary. A diagram has one of three forms:

- **Exit.** A boundary of the exits and a case of that boundary, with a port
  map that gives a port of the context to each port of that case.
- **Step.** An operation with a port of the context for each of its operands,
  and one diagram for each output case of the operation. The context of that
  diagram has the output ports of the case and the ports of the context.
- **Composite.** A first diagram, and then a continuation. The first boundary
  of the exits of the first diagram is the boundary of the continuation, and
  the other boundaries are the exits of the composite.

A continuation goes from a boundary to its exits. It has one of three forms:

- **Copairing.** One diagram for each case of the boundary. The context of
  that diagram has the ports of the case only.
- **Frame.** One diagram for all the cases of the boundary, with a bypass.
  The bypass is a boundary. Each case of the first boundary gives a case of
  the bypass with its ports, and it gives the ports of the one diagram. The
  one diagram has one boundary. A continuation follows, from the product of
  the bypass and that boundary.
- **Loop.** A body, which is a continuation from the boundary. The first
  boundary of the exits of the body is the boundary of the loop, and the
  other boundaries are the exits of the loop. An exit of the body to its
  first boundary is the next entrance of the loop.

The copairing is the universal property of the control sum, and the syntax
has no other selection. Two exits to one case are a join, and the syntax has
no merge operation. An exit to a later boundary of the list goes past the
continuation, so a continuation has only the paths that exit to its boundary.
An exit names its boundary by its position in the list. The meaning of a
composite thus finds the continuation of an exit by computation, for each
case.
A frame is the whiskering of a diagram by a boundary: the bypass keeps a
control case and its ports through the diagram.
A loop is the iteration `f†` of the feedback equation set. Its body is a
computation `f : A → B + A`: `A` is the boundary of the loop, and `B` is the
sum of the boundaries of its exits. The syntax has no other form of feedback.
A body can be a copairing, a frame, or a loop. A value that does not change
in a loop is a port of the entrance at each iteration, and the port map of
the exit to the entrance copies it.

The sources read one diagram in three ways. In the premonoidal calculus, a
step is an operation whiskered by its context, and the steps on a control
path are a sequence of whiskered operations. In the wiring of
Kondyrev–Spivak, a step is a box, its context is its bypass, and the exits
give the routing. A frame is a diagram in a box whose bypass has cases. An
exit of a loop body to the entrance is a wire from an output of an inner box
to an input of an inner box, and the trace of the wiring gives its meaning.
For Aberlé, a step is an element of the extension of the
signature polynomial at the ports of the context, and a diagram is an
implementation of its own interface in the `Free`/`FreeDep` core, with its
verification.

A diagram has an order of its steps on each control path. The order of the
effectful steps is the order on the runtime wire. The order of two steps that
no wire connects, when one of the two is pure, is not information: an
interchange derivation relates the two orders. A source diagram is a
presentation of a VSDG, and a VSDG has more than one presentation. The
derivations of a named equation set relate two presentations. A frontend
gives a source diagram. A realization is a presentation that
sequentialization selects by cost. Each of these diagrams has its
verification, by Aberlé's method.
[Where the sources meet](#where-the-sources-meet) gives the correspondences
that make this one system.
[Structure that the sources do not supply](#structure-that-the-sources-do-not-supply)
gives the parts of the integration that the construction must establish.

The implementation is correct by construction, with Aberlé's method. The
compiler is built in her category of specifications
(`def:abstract-framework`). An object is an interface with its specification,
and a morphism is an implementation with its verification
(`def:verified-impl`). The forgetful functor to her category of interfaces
gives the plain interface and the plain implementation. An operation has its
specification as a part of its signature: a precondition, and a postcondition
on each response that depends on the witness of the precondition. A diagram
has a specification of its own interface, from the specification of its
calls: a witness of its precondition has a witness of the precondition of
each call that a run can make, and its postcondition has the runs over that
witness. A verified diagram, for a specification of its interface, is a map
into the specification of the diagram: a witness of the precondition of the
diagram, and the postcondition at the result of each run. A step takes the
witness of the precondition of its operation from the context that the
diagram holds, and its continuation receives the postcondition of the
response. With a number of unrollings of each loop, a diagram is an
implementation of its interface by calls of the interface of its signature,
and a verified diagram gives that implementation with its verification. A
lowering is a verified implementation. A pass maps a verified object to a
verified object of the same specification. An agreement of the plain
computations is the plain part of a pass, and the evidence of a computation
moves along it. A derivation gives a map between the specifications of its
two diagrams, and a verified diagram moves along that map. Composition keeps
correctness (`thm:comp-dep`). A construction and its verification are built
in the same manner, and no stage is complete with the plain part only.

All definitions and laws are constructive. Each representation is selected so
that constructors and recursion build its evidence, and eliminators compute
on that evidence. [AGENTS.md](AGENTS.md) states the binding rules.

### Sources

The labels below are the labels in the source files. They identify the
constructions to implement and check in Lean.

#### Aberlé: implementations and their dependent verification

[Compositional Program Verification with Polynomial Functors in Dependent Type
Theory](https://arxiv.org/abs/2604.01303) supplies
the method of implementation and verification.

| Source construction | Implementation responsibility |
| --- | --- |
| `polynomial-functors`, `def:implementation` | A polynomial interface `(A, B)`; a lens with forward shape and backward response maps; an implementation `(a : A) → Free q (B a)` |
| `free-monads-and-sequential-composition` | Inductive return/request computations; structural bind and implementation substitution |
| `def:deppoly`, `⇒Dep` | `Pre a : Type` and `Post a pre b : Type`; a dependent morphism indexed by the particular implementation and supplied witness |
| `dependent-free-monads`, `def:verified-impl` | `FreeDep` indexed by a computation; return evidence, request admission evidence, and continuations that consume response evidence |
| `sumDep`, `compDep`, `thm:comp-dep` | Dependent composition along the same constructors as implementation composition; interface families and their specifications compose together |
| `example-fold-append-concat`, Appendix C, `foldInd` | A generic verified fold, relational append, and composed concat as the first complete instance |
| `def:mealy`, `def:depmealy`, `prop:prog-mealy-dep`, `state-invariants` | State transitions and invariant witnesses interpreted together; verification of a composed implementation gives verification of its execution |
| `def:abstract-framework` | Erasure of verified interfaces and implementations; compatibility of composition and interpretation |

- The paper calls `A` positions and `B a` directions. The Lean interface uses
  `Shape` and `Pos`.
- The paper's category of implementation interfaces, `Int`, is not the
  `Int(Poly_*)` construction of control wiring.
- The paper's module-composition trees are a verification construction. They
  are not the syntax of the traced IR, and they are not a scheduling hierarchy
  of the source.
- The paper's Agda development states no equation between programs.
  Specifications are relations, and each verification follows the recursion of
  its implementation. `thm:comp-dep` uses no monad law.

#### Kondyrev–Spivak: wiring, retained context, and execution

[Kondyrev–Spivak](https://arxiv.org/abs/2509.05462)
supplies the polynomial form of the syntax: boundaries, wiring, retained
context, feedback, and execution.

**Boundaries and routing.** A polynomial shape selects a control case. Its
ports are the data available in that case. A wiring morphism selects the next
case and supplies its data through backward port maps (`eqn.poly_map`). A
wiring morphism is natural in the data, so it cannot test a value. A box
filler can test, branch, and compute.

**Typed ports.** The multivariate construction `Set[L]` gives typed ports
for each category `L` of labels (text before `eqn.set_L_basics`). The design
has discrete labels, which are the value types. A port map is then a function
between ports: it copies, discards, and exchanges values, and it applies no
operation. A port map from a context `Γ` to a context `Δ` acts on a diagram
with the context `Δ`. The result is a diagram with the context `Γ`, and each
use of a port of `Δ` is the port of `Γ` that the map gives. A map of boundaries is forward on the cases and backward on the
ports (`eqn.poly_map`), and the first step of that formula is the universal
property of the sum. The forward map can send two cases to one case, which is
the join of two control paths. The backward map can give one source port to
two target ports, which is the copy of a value. One map thus has the two
structural rules. For finite boundaries, these maps are the free finite
coproduct completion of the free category with finite products on the value
types, which is the value category of an effect theory (Staton 2014, §3.3).
The trace of `cor.polystar_traced` applies to them. The monoidal product of
that trace is the sum, and a trace on a cocartesian category is equivalent to
an iteration operator from the maps `A → B + A` to the maps `A → B`
(`rem.iter`). The paper constructs the trace from that operator
(`prop.setstar_traced`). The loop of the design is that operator, and the
trace is a derived operation: `Tr(f) = inl ; (f ; (B + inr))†`
(Ghalayini–Krishnaswami 2024, equation 65). With a category of
labels, a port map also applies the maps
of `L` (`eqn.oplax_slice`, `rem.duc_query`). It gives one source port and one
map of `L` to each target port, so an operation with two inputs is not such
a map. Each operation of the design is thus a box.

**Composition.** The `Int` composition formula (`eqn.int_composite`) connects
open boundaries and traces over the internal interface. It defines
substitution. It selects no traversal, and a nested box is not an atomic
execution block. The execution formula (`lem.execution`, `eqn.execution`)
relates staged composition to one trace over all internal interfaces. It is
the proposed proof principle for the flattening of nested wiring with its
meaning preserved. It does not enumerate the schedules that a VSDG admits.

**Bypass.** The bypass operad `Para_×(Int(Poly_*))` (`def.para`, `eqn.w'`)
represents retained context compositionally. A bypass `M = Σ j, y^(A j)`
retains the case `j` and the data indexed by `A j` while a box executes at its
native interface. It can thus keep a branch distinction through
reconvergence. Nested substitution multiplies the outer and inner bypasses,
and it must reindex their cases, ports, and dependent specifications together.
The acting category is `Poly^≅`, so a bypass polynomial changes only by
isomorphism. The trace compatibility of `M × -` (`lem.polystar_dta`) is the
obligation that retained context survives feedback. The action of the paper is
the product of polynomials. The context of a step is the bypass of its box:
the port map into the box copies the operands, and the bypass keeps each port
of the context for the rest of the diagram. A bypass with more than one case
keeps a control case through a box, and the frame of the design has such a
bypass. The Lean construction
carries the unchanged context symbolically and does not enumerate its values.
These operations explain value availability. Physical storage and its cost
are lowering obligations.

**Algebras.** An algebra of the wiring operad supplies box meanings and an
interpretation that respects substitution (`sec.w_alg_cats`,
`eqn.partial_fn_algebra`). It separates wiring from primitive computation and
requires their composition law. Two cautions apply. The tensor of
`Int(Poly_*)` is written `+`, but `Int(Poly_*)` is not cocartesian. The
commutative monoids that an algebra supplies merge control alternatives
(`prop.supply_monoids`); they are not the value comonoids that copy and
discard data. Neither structure permits duplication of the runtime.

**Cells.** The double category gives a form for local compatibility evidence
(`thm.IInt`, `eqn.cell`). Loose maps are wiring diagrams. Tight maps adapt
input and output interfaces. A cell is the commuting square between them.
Such squares are candidates for certified boundary reindexing and for changes
of loop representation. Horizontal pasting depends on uniformity: a
compatible change to the internal feedback interface must preserve its trace
(`def.strict_uniform`). The trace axioms do not give that result, and strict
maps in a traced category need not compose (`warn.cant_compose_strict`). The
uniformity and pasting laws must be proved for the implemented domain before
transformation composition uses them. A commuting square also needs a
dependent evidence map before it can transport a specification.

**Execution.** The step and remainder factorizations, the trajectory logs, and
the adequacy theorem (`thm.operational`, `cor.corners_log`, `thm.adequacy`,
`cor.adequacy_sem`) give the form of an execution certificate. A certificate
records boundary crossings and their payloads, and it justifies the
interpreter's result against the filled diagram. The work starts with finite
routing and examples without feedback, and it connects the runs of loops
later.

#### Román–Sobociński: the runtime and the scope of rewrites

[Román–Sobociński](https://arxiv.org/abs/2305.06075)
supplies the laws of the syntax for effects. A diagram without a test is one
of its string diagrams: a sequence of whiskered operations. Its structure is
an effectful category: a selected monoidal category of pure maps, included
centrally in a premonoidal category of computations (`sec:effectfulcats`).
The selection matters. A state operation is not pure because it
commutes with one other operation in one model. Interpretations preserve the
designated pure maps. Each additional commutation needs its own evidence.

**Runtime.** `theorem:runtime-as-a-resource` represents the calculus with
diagrams. Pure generators act on value wires. An effectful generator `A → B`
has one more input and output for the runtime, `R ⊗ A → R ⊗ B`. No generator
copies or discards `R`. Runtime braidings move this wire past value wires, and
braid-clique coherence makes its position irrelevant. In the implementation,
the runtime is in the runner and not in a port: a state model gives
`R × ⟦Γ⟧` to a context `Γ`, and the continuation of a call keeps the context.
No map of the implementation moves the runtime past a value.

**Sequencing.** Composition joins the one runtime output to the next runtime
input. Whiskering carries unrelated values past one computation. The tensor of
two effectful implementations would need two runtimes, so it does not define
their execution on a shared runtime. Arbitrary effects thus do not satisfy
interchange, and a pure map moves across an independent effect by centrality
(`sec:premonoidalcats`, `lemma:eff-is-premonoidal`). Sequentialization can
therefore change the position of pure work, and it cannot reverse the order of
effects without an effect law. The free-effectful-category theorem guides the
syntax and the interpreter laws. It does not say that an arbitrary state
runner satisfies them. Rewrites are explicit structural derivations that the
`Free`/`FreeDep` core interprets, with dependent evidence maps. There is no
quotient of programs and no second verification engine.

**Global state.** The global-state theory (`sec:exampleGlobalState`,
`fig:axioms-global-state`) combines value copy and discard with `get` and
`put`. A read is a coaction `R → R ⊗ X`; it is not a copy of the runtime. The
equations say:

- two reads return the same value;
- a discarded read does nothing;
- of two writes, the last one stays;
- a read followed by a write of that value does nothing;
- a write followed by a read returns the written value.

The implementation instantiates these equations constructively for the
selected single-process store, and each rewrite that it uses is a map of
verified computations. The equations depend on that effect theory and observation
contract. Observable read/write events, failure, or interference can
invalidate an equation that holds for returned values and final store.

For VSDG sharing, this separates the copy of a produced value from the
duplication of its producer. A `get` result can be retained and copied as a
value. A second `get` after a `put` can return a different value. The pure
comonoid laws therefore do not permit common-subexpression elimination or
speculation of stateful operations. The paper's race-condition example is a
negative check for unsupported reordering; it is not a requirement for a
concurrent execution engine. Independence of distinct resources needs an
explicit resource decomposition and proofs that the operations commute. It
does not follow from separation in a diagram.

#### Lawrence: the source and the choices that it leaves open

[Lawrence's thesis](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-705.pdf)
is the source reference. The [source contracts](NOTES.md#source-contracts)
give its concrete assumptions and instruction counts.

- A VSDG records values, their unique producers, ordered operands, and state
  edges that are used linearly (§2.6). In each execution, the stateful
  operations are totally ordered (Appendix B.4).
- A VSDG specifies the values that the result uses. It does not specify which
  operations execute, or their order (§2.2.3). The thesis reads a VSDG as a
  lazy functional program and a CFG as a strict one.
- A γ-node selects between two tuples of operands, and a tuple can contain the
  state (§2.6.2). Its two reduction rules use the selected operand only
  (§2.7.2). A γ-node on the state is a conditional in the state monad
  (Appendix B.2).
- A state edge marks each operation that has a side effect or that can fail to
  terminate. Each other operation can be speculated (§2.2.3). The thesis
  prefers an explicit test before an operation that can raise an exception.
  That operation has no state edge, and its speculation is an open issue of
  the thesis (Appendix B.7).
- Sequentialization narrows a set of traces, and the observable result stays
  the same (§2.7.1). The trace set ranges over orders, evaluation strategies,
  hash-consing, and node cloning (§2.7.3).
- The thesis divides sequentialization into three selections: an evaluation
  strategy, the duplication that one program counter needs, and a total order
  with registers (§2.4).
- A CFG node stores one continuation. A node with `i` distinct continuations
  needs `i` copies (§2.4.3).
- Sharing is an explicit partition of an unshared graph. Reuse sharing relates
  computations with identical histories. Tail sharing relates computations
  with identical futures (§5.2).
- Loop transformations are sharing partitions on the infinite unfolding of the
  loop (§5.4).
- The RVSDG hierarchy records control dependence, which is a selected
  evaluation strategy (§5.5).
- The VSDG has the form of a Petri net. Its semantics are not Petri-net
  semantics (§2.6, footnote 13).

### Where the sources meet

| Lawrence | Román–Sobociński | Kondyrev–Spivak | Aberlé |
| --- | --- | --- | --- |
| State edge, used linearly | Runtime wire `R` | `R ×` in the values of each control case | State of the runner |
| Value that is live across an operation | Whiskering `M ⊗ f` | Bypass `M × P` | Context that the continuation holds |
| Stored continuation (§2.4.3, §5.1) | — | Bypass case `j` | — |
| γ-node: a test, and the tail-shared places of each component (§5.2) | — | A box with a sum output, the copairing over its cases, and a forward map that sends two exits to one case | Continuation of a request, with one case for each response |
| Tail sharing: identical futures | — | Forward map sends two exits to one entrance, and the merge `∇` | Continuation of a `bind` |
| Reuse sharing: identical histories | Copy `Δ` of a value | Backward map connects two ports to one producer | — |

- **The steps have an order.** A morphism of `W` routes control through one
  box at a time, so it gives an order to its boxes. Each operation of a
  diagram is a box, so a diagram has an order of its steps on each control
  path. The order of the effectful steps is the order on the runtime wire.
  The order of two steps that no wire connects, when one of the two is pure,
  is evidence that the dependencies have no cycle, and it is no other
  information. An interchange derivation relates two such orders.
- **A step has three descriptions.** A step is a box of the wiring, a
  whiskered operation of the premonoidal calculus, and an element of the
  extension of the signature polynomial at the ports of its context. The
  interpretation gives one computation to the three, which is a request of
  Aberlé's interface.
- **A sequence of boxes is a premonoidal word.** A `W′` diagram that visits
  its boxes in one sequence is a sequence of whiskered operations
  `M i ⊗ f i`. The bypass `M i` is the context of step `i`. The cut of values
  that are live across the step is the part of the context that a later step
  or exit uses.
- **A polynomial has the two structural rules.** `Σ i, y^(A i)` is a sum of
  control cases with a product of data in each case. A map of polynomials is
  forward on the cases and backward on the ports. Backward, two ports can
  have one source port: this is the copy `Δ`, and reuse sharing uses it.
  Forward, two cases can go to one case: this is the merge `∇`, and tail
  sharing uses it. The two rules are dual. The naturality of the copy holds
  for the named operations only. The naturality of the merge is
  `[f ; h, g ; h] = [f, g] ; h` for each `h`. With the unit and coherence
  laws, it is equivalent to the universal property of the control sum
  (Bonchi–Cioffo–Di Giorgio–Di Lavore 2025, Definition 2).
- **A γ-node has no node.** A γ-node is a test and a join: the true operand,
  the false operand, and the result of each of its components are tail-shared
  places (§5.2). The test is an operation with a sum output, and the
  copairing gives one diagram to each of its cases. The two diagrams exit to
  one case of a boundary. The ports of that case are the results of the
  γ-node, and the port maps of the two exits are its two operand tuples. The
  consumers of the results are in the diagram that a composite gives to that
  case.
- **The runtime wire follows control.** The runtime is not a port. A state
  model gives the values `R × ⟦Γ⟧` to a case with the ports `Γ`, and the sum
  of cases distributes: `R × (A + B) ≅ (R × A) + (R × B)`. Control is in one
  case at a time, and a diagram goes from one step to the next step on one
  path. Copy and discard are maps on value ports. A diagram thus cannot copy
  or discard the runtime. The state edge of the VSDG, the runtime wire of the
  string diagram, and the thread of control through the diagram are one wire.
- **A shared operator needs one future or a record of its past.** Two paths
  can exit to one case when they have the same continuation. If they do not,
  a frame has one copy of the shared diagram, and its bypass has one case for
  each path. The continuation after the frame reads that case. A path that
  does not use the shared diagram exits past the frame. A CFG node
  stores one continuation (§2.4.3), so a frame is not a choice of the thesis.
  The stored case has a cost: a tag with a test, or a return address (§5.1).
- **Each sharing has a form and a law.** Reuse sharing is two ports with one
  producer, and copy naturality gives the two operations. Tail sharing is a
  composite, and the naturality of the merge gives the continuation at each
  exit. A stored continuation is a frame, and the preservation of the sum by
  whiskering gives a copy of the diagram for each case of the bypass.

The stages in [PLAN.md](PLAN.md) construct these correspondences. The two
sharing rows are hypotheses that the control-and-sharing stage tests against
Figures 5.6 and 5.7. No row has a proof in this repository until its stage is
complete.

### Source object and admissible realizations

**Signature.** An operation signature gives the value types and the
operations. Each operation has a product of typed input ports and a
polynomial output boundary: a sum of control cases, with a product of typed
ports in each case. A pure operation is a total function from its inputs to
its output boundary. An
effectful operation has the runtime wire as one more input and output, and the
runtime wire is the state edge of the VSDG. A test is an operation whose
output boundary has two or more cases.

The signature gives one of three forms to an operation that can fail:

- a total operation, with a defined result for each input;
- an effectful operation, with the failure as an effect on the runtime;
- a guarded operation, whose input port type exists only in one case of a
  test.

A guarded operation cannot be before its test, because its input does not
exist there. The absence of a state edge does not make an operation total. The
thesis prefers an explicit test before an operation that can raise an
exception, and that operation has no state edge (Appendix B.7).

A source division that fails for a zero divisor is a test for a zero divisor,
with the failure effect of the source language in one case and a guarded
division in the other case. The guarded division has no zero divisor as an
input, so the result of a target instruction for a zero divisor has no
observation. The
[Stele and EVM contract](NOTES.md#stele-and-evm-failure-gas-and-loops) gives
an example: a Stele division reverts for a zero divisor, and EVM `DIV`
returns zero.

**Source object.** The source of a translation is a diagram over the
signature. Its structures are the operations, the value tensor with copy and
discard on each value wire, the runtime wire, and the control sum with its
injections and copairing. Each operation is a step, and the exit boundary of
a diagram is a polynomial boundary.

Selection is the copairing `[f, g]`, which has one diagram for each case of a
sum. No operation selects. The sum is the sum of polynomial boundaries, and
the design has no other sum. A predicate is the output case of a test, and the
distribution `Γ ⊗ (A + B) ≅ (Γ ⊗ A) + (Γ ⊗ B)` gives the retained values `Γ`
to each case. The diagrams of the output cases of a test are the copairing. A
copairing of pure diagrams selects values. A copairing of effectful diagrams
selects the continuation of the runtime.

A join is two exits to one case of a boundary. No operation merges. The ports
of the case are the values that the two paths give, and the port map of each
exit selects them from its context. A composite gives one diagram to the
case, which is the one continuation of the two paths. That diagram has the
ports of the case only, so the port map of an exit is the cut of the values
that are live after it. Each γ-node of a VSDG becomes a test, the copairing
over its cases, and a join.

A diagram records producers and ordered operands: each operand of a step is
a port of its context, and each port has one producer. It records an order of
the steps on each control path, and the order of the effectful steps is the
order on the runtime wire. It records the case of each operation: an
operation is before a test, or it is in a case of that test. It records each
continuation that two paths share, and each diagram that a frame shares
between paths with different continuations.

A source diagram is a presentation of a VSDG, and a VSDG has more than one.
The translation makes four selections that the VSDG does not make: the order
of two operations that no wire connects, the case of each operation, the
continuations that two paths share, and the diagrams that a frame shares. A
structural relation with explicit derivations relates two presentations of
one VSDG, and each theorem names the
equation set of the derivations that it uses.

In the interchange equation set, a pure operation is central. An interchange
derivation thus relates the two orders of two steps that no wire connects,
when one of the two is pure. With the control equation set, the two steps can
be two pure tests. The order of two effectful operations is on the runtime
wire, and it is source information.

The equation set of a theorem decides if the case of an operation is source
information:

| Operation | Is its case source information? |
| --- | --- |
| Effectful | Yes. The copairing on the runtime fixes it. |
| Pure, when the theorem keeps its execution count | Yes. |
| Pure, named for discard naturality | No. Each case in which its inputs exist gives the same meaning. |

For the operations of the third row, a flat VSDG, a nested hierarchy of cases,
and the unshared form are presentations of one source. The unshared form has
one diagram without selection for each control path. It corresponds to the
unshared graph on which the thesis defines sharing (§5.2). Position invariance
is an obligation with a proof. It is not a rule of syntax.

**Realization.** A realization of a source diagram is a diagram with a
derivation from the source diagram, in a named equation set. Each diagram is
a `W′` diagram of Kondyrev–Spivak with discrete type labels and a filler for
each box: each step is a box, and each port map only copies, discards, and
exchanges ports. Its steps give the operation order on each control path. Its
contexts give the retained values. Its boundaries and the bypasses of its
frames give the retained control cases.

**Sequentialization.** Sequentialization selects a realization of a source
diagram by cost. It selects the order of the steps, the case of each
operation, the copies of each operation, the continuations that two paths
share, and the frames. Each selection is a derivation, so each diagram
between the source diagram and the realization is a diagram of the same
syntax.

**Soundness.** A realization is sound for an equation set when its meaning
equals the meaning of the source diagram in each interpretation that satisfies
the set. One interpretation of the syntax gives the two meanings. The
soundness of each derivation rule gives the soundness of each realization.
Each soundness theorem names its equation set and its observation.

| Equation set | Equations | Choices that it permits | Observation that it keeps |
| --- | --- | --- | --- |
| Interchange | Pure operations are central. Copy and discard are a commutative comonoid on each value. | Each order that respects the wires | Returned values, runtime, order of effectful operations, and one execution of each occurrence |
| Copy naturality, for named operations | `f ; Δ = Δ ; (f ⊗ f)` | Merge and duplication of those operations: hash-consing, node cloning, reuse sharing | As above, without the execution count of the named operations |
| Discard naturality, for named operations | `f ; ε = ε` | Removal and speculation of those operations | Returned values, runtime, and order of effectful operations |
| Control | The control sum is a coproduct in the category of computations: `inl ; [f, g] = f`, `inr ; [f, g] = g`, and a map out of a sum is fixed by its two cases. Whiskering preserves the sum. | Merge, tail sharing, and tail duplication. With discard naturality: branch placement. | Returned values, runtime, and order of effectful operations. Static size and moves are costs. |
| Feedback | The loop `f†` of a body `f : A → B + A` is the initial fixed point in the category of computations: `f† = f ; [id, f†]`, and each computation `g` with a map `f ; [id, g] ≤ g` has exactly one map `f† ≤ g` that commutes with the fixpoint maps. Whiskering preserves the loop. | Loop cuts: unpeeling, unrolling, pipelining, and the placement of invariant operations | Returned values, runtime, order of effectful operations, and the existence of a run. The number of iterations is not an observation. |

A pure operation is a total function, so it can be named for copy naturality
and for discard naturality. A theorem that keeps the execution count of an
operation does not name it. A guarded operation can be named, and its input
type keeps it in the case of its test. An operation on the runtime wire is in
neither set. Its equations come from its effect theory, for example the
global-state equations.

Each equation set is the theory of a kind of category:

- interchange: an effectful category with copy and discard on values
  (Román–Sobociński);
- copy and discard naturality for each pure operation: a Freyd category, whose
  pure part is cartesian;
- control: a control sum that is a coproduct, which the inclusion of the pure
  maps and whiskering preserve. With a cartesian pure part, this is a
  distributive Freyd category (Staton 2014, Definition 3.4): a distributive
  category of values, a category of computations with finite coproducts, an
  action of the values that preserves those coproducts, and an
  identity-on-objects functor that preserves the action and the coproducts;
- feedback: the above with a strong Elgot structure (Ghalayini–Krishnaswami
  2024, §5.1): an iteration operator with the fixpoint, naturality, and
  codiagonal laws, uniformity for the pure maps, and preservation by
  whiskering.

The meaning of a source diagram in a model of one kind is a recursion on the
diagram.

The control equation set is a universal property, and no stage selects it. It
gives `[f, g] ; h = [f ; h, g ; h]` for each `h`, pure or effectful. Read from
right to left, this equation is tail sharing. Read from left to right, it is
tail duplication. In the syntax, the left side is a composite, and the right
side has the diagram `h` at each exit. The equation is the naturality of the
merge `∇`. The preservation of the sum by whiskering relates a frame to the
copairing that has a copy of its diagram for each case of the bypass. The
Kleisli category of a monad on a category with
coproducts has those coproducts (Kondyrev–Spivak, proof of
`prop.setstar_traced`). The category of an arbitrary algebra of the wiring
operad keeps the merge and can lose the universal property (remark after
`prop.supply_monoids`). The property is thus an obligation for the implemented
algebra, with a proof for the runner.

The thesis is the agreement test for the control equation set:

- the two reduction rules of a γ-node are the first two equations (§2.7.2);
- tail sharing has no purity condition, and it relates computations at
  different leaves of a γ-tree (§5.2);
- a stateful operation has no reuse sharing, because it cannot be applied to
  two states (Appendix B.4);
- speculation is for operations that have no side effect and that terminate
  (§2.2.3). A write is not in the discard set, and a guarded operation stays
  in the case of its test (Appendix B.7).

The feedback equation set is a universal property too. A computation is a
Type-valued relation between inputs and results, and its elements are runs.
`g ≤ h` is a map from the runs of `g` to the runs of `h`. Two computations
agree when their run families are equivalent: a map in each direction, with
the two round-trip identities at each run. The loop of a body is the initial
computation that the fixpoint equation closes. The map from the loop to each
other such computation exists, and it is unique at each run. The laws of a
strong Elgot structure are consequences: naturality, codiagonal,
dinaturality, uniformity for the pure maps, and preservation by whiskering.
Each law is an equivalence of run families, and each is an obligation with a
proof by induction on runs. A postcondition that depends on a run moves
across a law by transport along the round-trip identity. A soundness theorem
that uses only these laws holds in each model with a strong Elgot structure.

In the syntax, the fixpoint equation relates two composites. The left side
is a first diagram and then the loop. The right side is that first diagram,
then the body, and then the loop. The trace laws are consequences of the
feedback equation set, because the trace is a derived operation of the loop.

The two meanings of a diagram give two statements of soundness. The first
statement is for the function meaning: for a rule of the interchange, copy,
discard, or control equation set, the function meanings of the two diagrams
agree for each number of unrollings. The second statement is for the
specification. A rule holds for a specification of the calls when it has a
map between the specifications of its two diagrams, in each direction: a
witness of the precondition of one diagram gives a witness of the
precondition of the other, and each run over the second witness gives a run
over the first witness to the same result. A derivation in a rule set that
holds for a specification of the calls has these maps, and a verified diagram
moves along them to a verified diagram of the same specification. The first
statement is the plain part of that pass. A rule of the feedback equation set
changes the number of unrollings that a run needs, so it has the second
statement only. The condition on the specification of the calls for which a
rule set holds is an obligation of the stage of that rule set.

The thesis is the agreement test for the feedback equation set. The stage
that constructs the equations derives each loop choice of §5.4 from them:

- unpeeling is the fixpoint equation;
- unrolling at a distance of two iterations is `(f ; [inl, f])† = f†`, and a
  larger distance repeats the composite;
- software pipelining is dinaturality, with discard naturality for each
  operation that it speculates;
- the placement of an invariant operation is copy naturality across
  iterations, through uniformity for a pure map and preservation by
  whiskering. Without an unpeeled first iteration, it also needs discard
  naturality for that operation.

**Coverage.** Each choice that the thesis leaves open must have a
realization:

- each dependency-respecting order of fixed occurrences (§2.2.2, §2.7.1);
- each well-formed reuse and tail sharing partition, with Figure 5.6 and the
  five arrangements of Figure 5.7 (§§5.2–5.3);
- the evaluation strategies and the finite speculation that keep termination
  (§2.2.3, §2.7.2);
- the loop cuts of §5.4.

The list comes from the thesis. It does not depend on the generator of
realizations, and completeness for a target grammar is not coverage. It does
not depend on the presentation of the source: each order of two tests that no
wire connects is a dependency-respecting order. A
generator that omits one of these choices restricts the source. The premises
treat that restriction as a departure.

**Opportunities.** A realization that is sound for a named equation set and
that is not one of the thesis choices is an opportunity. The premises require
its benefit, its costs, and the preserved baseline. A frame whose bypass has
more than one case is an opportunity: the thesis expects more tests or a copy
of the operation from a stored return address (§5.1).

Soundness and coverage are separate proofs. Both are required for each
claimed fragment. The reduction system of the thesis (§2.7.2) is the reference
for the observable result. The implementation does not execute it.

### Frontends and backends

The theorems of the IR are for each interpretation that satisfies a named
equation set. A frontend and a backend connect a language to those theorems.
No language defines an observation of the IR.

A frontend supplies:

- a signature: the value types, the operations with their forms, and the
  failure effects of the source language;
- a translation from source programs to source diagrams;
- the correspondence between the semantics of the source language and the
  meaning of the diagram.

A backend supplies:

- an interpretation of the signature in the target language, with an
  agreement relation on target computations;
- a proof that each named equation set holds under that agreement relation;
- a machine model, which the placement obligations, the storage obligations,
  and each cost comparison use;
- a sufficiency statement, if the target has a bounded resource;
- a proof that the lowering causes no failure that only the target has.

**Resources.** A bounded resource of a target, such as EVM gas, belongs to
that target's semantics and cost model. A resource sufficiency statement is a
condition of the backend's preservation theorem: for each terminating source
run covered by the statement, a bound exists above which the target run has
the related result. It need not be one bound for all inputs or a bound known
at compile time. A bound computed from the source run is a further result.

These target conditions do not restrict the IR to terminating programs or to
programs with an execution budget. A RISC-V backend supplies its own machine
and execution environment contract; it does not inherit EVM gas semantics.
Evaluator fuel is separate from target resources and is not an implicit
counter in generated code.

**Directions.** Agreement of two diagrams inside the IR is a map between
their specifications in each direction. Each boundary states its directions. The direction from target runs to source
runs is necessary for each pair. The direction from source runs to target
runs has a resource sufficiency condition when the backend contract requires
it. A source semantics with free choices, such as a read of the available
resource, can give the first direction only.

**Costs.** The cost model of a comparison is the machine model of its
backend. The register-machine counts of the thesis are the agreement test for
the sharing choices.

**The example pair.** Stele is the example frontend, and the EVM is the
example backend. The
[Stele and EVM contract](NOTES.md#stele-and-evm-failure-gas-and-loops) gives
their facts. The refinement relation of EquiVM is a result at the boundary of
this pair. It is the direction from target runs to source runs, and it has no
constraint for a run that ends with out-of-gas. Gas is the bounded resource,
and the machine model is a stack machine. The failures that the lowering
excludes are stack underflow, stack overflow, and a bad jump destination.

### Structure that the sources do not supply

The premises treat the sufficiency of the foundations as a hypothesis. Each
item below is an obligation of the construction, and none is an assumption.

1. Román–Sobociński have no coproduct, no distributivity, and no trace. The
   relation between the runtime, the value tensor, and the control sum is new
   structure. The control equation set states it, and its proof for the
   implemented runner is an obligation.
2. The effectful algebra of the wiring operad is a construction to establish,
   as a verified implementation. Equal boundary types do not supply it.
3. `Free` computations are well-founded, and Aberlé's Mealy machines are Agda
   coinductive records. Lean needs an explicit representation for loops.
4. Kondyrev–Spivak obtain the polynomial trace through a fully faithful
   embedding into functor categories and iteration on partial functions. Lean
   must construct the shape and port result and its structural evidence
   directly.
5. The partial-function semantics of Kondyrev–Spivak identifies unsuccessful
   execution with infinite execution. Finer failure and divergence
   observations need their own preservation results.
6. The double category of Kondyrev–Spivak is thin, because commutation is a
   property. The Lean witnesses have computational content. The square and its
   pasting operations are implemented without identification of all witnesses.
7. A loop of the thesis is an infinite unfolding with a lazy selection. The
   polynomial trace is control iteration. They agree only after the selection
   of an evaluation strategy.
8. The thesis leaves two items informal: the relation between reduction steps
   and program operations (§2.7.3, footnote 18), and an internal form of the
   speculative-write restriction, which §5.3 defines through the produced PDG.
9. The thesis counts instructions for a register machine. A target supplies
   its machine model, and each cost comparison names that model. The EVM has
   an operand stack. On a stack machine, a value that is live across an
   operation is a stack item below the operands, and its cost depends on the
   operation order through the duplicate and swap instructions. The equal
   registers of a γ component become equal stack layouts at a merge.
10. No source gives one category with the value tensor, the runtime, and the
    control sum, or a normal form for its diagrams. The universal property of
    the source diagrams, the unshared form, and position invariance are
    constructions to establish. The
    [reference files](NOTES.md#reference-files) give the category and a
    presentation of it by terms. They give no presentation by diagrams:
    - Ghalayini–Krishnaswami 2024 define the distributive Freyd category
      with a strong Elgot structure (§5.1): a premonoidal category with a
      cartesian subcategory of pure maps, coproducts with an invertible
      distributor, and an iteration operator that is uniform for the pure
      maps and that whiskering preserves. SSA regions modulo an equational
      theory are the initial model (Theorems 5.13 and 5.15). In that theory,
      each region is equal to an A-normal form, to a strict SSA region, and
      to a structured region (Lemmas 4.4 to 4.7, Theorem 4.8). A region has
      an order of its `let` bindings, as a diagram of the design has. An
      A-normal form has one operation on variables in each binding, which is
      a step. A `where` block is a composite (rule `cfg`): its labels are
      the cases of the boundary of the continuation, and the outer labels of
      its body are the cases of the other boundaries of the exits. The exits
      of a diagram are the label context of that rule. The continuation of a
      `where` block without recursion is a copairing. With recursion, it is
      the loop of a copairing, and a branch of a block to a label of its
      `where` is an exit to the first boundary of the body. Rules `cfg-β₁`
      and `cfg-β₂` are the two exit equations. Each block of a `where` keeps
      the variables of the context, and the meaning of the rule is the
      iteration with a context that does not change (`rfix`, equation 64). A
      continuation of the design has the ports of its case only, so the loop
      of the design is the iteration without that context. The theory has two classes of
      operation, pure and impure, and each pure operation can be copied and
      discarded. The interchange of two bindings is thus a consequence
      there, and it is a derivation rule of the design. The initial model is
      a quotient of the syntax.
    - Staton 2014 defines the distributive Freyd category. It gives no free
      construction and no normal form, and it names the Kleisli category of a
      strong monad as an example for the case without coproducts only.
    - Jeffrey 1997 has three classes of node: value nodes that can be
      duplicated and discarded, central nodes that can change order only, and
      process nodes on the control line. These classes are the rows of the
      case table of the source object: an operation that is named for copy
      and discard naturality, an operation with the interchange equations
      only, and an effectful operation. The paper leaves coproducts in each
      category and a trace on processes as future work (§9.3).
    - The tape-diagram papers present rig categories, whose objects are sums
      of products. Bonchi–Di Giorgio–Santamaria 2022 need a biproduct for
      the matrix form of an arrow, and they say that a function
      `A × B → X + Y` of `Set` has no tape diagram. Bonchi–Cioffo–Di
      Giorgio–Di Lavore 2025 have a control sum that is a coproduct, for
      symmetric monoidal monads only. They define the coproduct by a natural
      monoid on each object, which is the merge (Definition 2), and the
      comonoids of their tensor are not natural (Definition 12). No
      tape-diagram paper has a state effect without interchange.
11. The sources and the reference files do not give a constructive meaning
    for a loop with effects.
    - Kondyrev–Spivak define the trace on partial maps as the value at the
      least number of steps, and as undefined when no such number exists
      (`prop.setstar_traced`). They define the result of a run as the value
      of its last configuration when the run is finite, and as undefined when
      it is not (`def.run`). Each definition has a case split on termination,
      which a constructive function cannot make. The positive part of each
      definition is an inductive reachability relation.
    - A complete Elgot monad has an iteration operator on its Kleisli
      category, for a body `X → T (Y + X)`, with fixpoint, naturality,
      codiagonal, and uniformity laws (Goncharov–Milius–Rauch 2016,
      Definition 2). Uniformity is for the maps of the base category. This is
      the published form of the feedback equation set for effects. A monad
      `U T F` for an adjunction `F ⊣ U` and an Elgot monad `T` is an Elgot
      monad (Goncharov–Schröder–Rauch–Piróg 2019, Theorem 6.2). The state
      transformer `X ↦ (S → T (S × X))` has that form.
    - Ghalayini–Krishnaswami 2024 give the Kleisli category of a strong
      Elgot monad as a model, with the state transformer as an example
      (§6.1). In their theory, uniformity is for the pure maps, and
      dinaturality is for each map. Their iteration for the option monad has
      a case split on the existence of a number of steps. They name guarded
      iteration as future work for languages that terminate (§7.4).
    - On `Set`, the maybe monad is a complete Elgot monad, and its operator
      is a least fixed point. The 2019 paper gives the belief that, in a
      category with a nonclassical internal logic, the delay monad is not an
      Elgot monad in general and the initial Elgot monad is not the maybe
      monad (Remark 5.16).
    - Benton–Hyland 2003 define a trace on a premonoidal category for
      recursion over values. Their state example does not carry the state
      around the loop. It is not the structure for a control loop with a
      changing runtime.
12. No source gives the diagrams of the design with their derivations.
    Kondyrev–Spivak give the wiring with typed ports and its trace
    (`cor.polystar_traced`). Ghalayini–Krishnaswami give the let form, with
    equations for two classes of operation. The diagrams of the design are a
    candidate for the presentation by diagrams that item 10 names. Three
    parts are constructions to establish:
    - The correspondence of a diagram with a `W′` wiring diagram. Each step
      is a box, its context is its bypass, and the exits and the composites
      are the routing. A frame is a diagram in a box whose bypass has cases.
      The action of a bypass is the product of polynomials
      (`lem.polystar_dta`), and its compatibility with the trace is an
      obligation of the stage with feedback.
    - The derivation rules of each equation set, with the soundness of each
      rule: the interchange of two steps that no wire connects, the copy and
      the removal of a named operation, the case of an operation, the
      shared and the copied form of a continuation, and a frame and its
      copies.
    - The orders of a diagram. The diagrams that the interchange derivations
      relate to a diagram are the orders of its steps that respect the wires
      and the runtime wire.

### Representation decisions

#### Interfaces, identity, and observations

A polynomial stores its shape and position types. A morphism stores its
forward shape map and its backward position map, and its action on values is
derived from those maps. Products, sums, dependent families, partial maps, and
reindexing are defined on this data directly. Morphisms are not reconstructed
from natural actions on function-valued extensions through extensional
equality.

Type-valued identity is used for individual data and for index transport, with
computational eliminators. Agreement of functions is pointwise. Agreement of
polynomial morphisms consists of shape identities and the corresponding
transported position identities. Agreement of computations follows requests,
responses, and results. Each relation needs composition, congruence, and the
applicable round-trip laws. Category and operad laws use these
correspondences. They do not need equality of whole functions or of proof
objects.

The [Prelude container interfaces](Prelude/Container.lean) implement this
representation. The component of a morphism at one source shape is an
extension of the target container. Structural agreement uses the relation
`Ext.Agreement`, which aligns shapes and supplies one response path for each
port. The [dependent consumer](Prelude/Container/Section.lean) reindexes
evidence about individual responses and keeps the exact input and precondition
witness. It is the closed, one-call case of Aberlé's dependent morphism.
Admission and response evidence for open computations belong to `FreeDep`.

Each consumer of related objects must be addressed. A higher-order primitive
or a dependent specification does not automatically respect pointwise
agreement. Call verification is indexed by the actual routed payload and the
supplied evidence. An operation that reindexes or transforms a call must
construct the necessary evidence maps. An additional law of a primitive
interface needs constructive implementations in the supported examples. An
extensionality oracle in the form of a parameter is forbidden.

Finite-source operations receive a typed operand telescope, so that
coordinatewise identities construct the identity of the finite operand data.
Port valuation and tabulation adapters need explicit round trips, and they
must preserve the source observation. This representation must cover the
intended VSDG operations with their semantics unchanged. General polynomial
interfaces keep arbitrary position types. Finite control does not imply finite
data or finite response types.

#### Implementations and specifications

`Free` and `FreeDep` are one computational core. The object of the compiler
is the verified implementation: an implementation with its evidence, as one
object. Bind, substitution, interface sums, and multiary composition
construct the two by the same constructors, so a composite of verified
objects is a verified object. The implementation is the index of its
evidence, and it is the image of the verified implementation in the category
of interfaces. Precondition witnesses are kept, and a postcondition can
inspect their constructors and payloads. A runtime-indexed weakest-precondition
API, if it is useful, is an adapter with computational round trips. It is not
a second verification engine.

The first examples compose `foldInd`, append, and concat, and they recover the
ordinary results by elimination of the relational evidence. A second example
uses two distinguishable admission witnesses for one input, passes returned
evidence into a later request, and consumes it after repeated substitution.
Both witnesses must stay available. Unit-valued specifications cannot validate
the representation.

#### Diagrams

Diagrams and continuations are two inductive types that refer to each other.
A diagram has three constructors: the exit, the step, and the composite. A
continuation has three constructors: the copairing, the frame, and the loop.
A context is
a list of value types, and a port is a position in that list. A boundary is a
list of contexts, and a case is a position in that list. The exits of a
diagram are a list of boundaries, and an exit names its boundary by a
position in that list. The product of two
boundaries has the concatenation of the two contexts for each pair of cases.
The diagrams of a step and of a copairing are a function of the case. An
exit has a boundary of the exits, a case of that boundary, and a port of the
context for each port of that case. A step has an operation and a port of the
context for each
operand, which is an element of the extension of the signature polynomial at
the ports. It has one diagram for each output case, in the context with the
output ports of that case. A composite has a first diagram and a
continuation. The exits of the first diagram are the boundary of the
continuation, and then the exits of the composite. A
copairing has one diagram for each case of
its boundary, in the context of that case. A frame has a bypass, one diagram
with one boundary, and a continuation from the product of the bypass and that
boundary. For each case of its boundary, it has a case of the bypass with
a port for each port of that case, and a port for each port of the context of
its diagram. A loop has a body: a continuation from the boundary of the loop,
whose exits are that boundary and then the exits of the loop.

A diagram has two meanings: the function meaning and the specification. Each
is a structural recursion on the diagram.

The function meaning is a recursion into the `Free`/`FreeDep` core, with
the remaining computation as an argument. A step is a request of the
interface of the signature at the values, and a request has a continuation
with one case for each response. The continuation of a request is thus the
copairing, and the core needs no other construct for selection. An exit gives
its case and its values to the remaining computation. A composite gives a
remaining computation to its first diagram: the meaning of its continuation
at an exit to the boundary of the continuation, and the remaining computation
of the composite at each other exit. A copairing gives the values of a case
to the diagram of that case. A frame gives the selected values to its one
diagram. It then gives the case of the bypass, the kept values, and the exit
of that diagram to its continuation. The two exit equations of the control
sum hold by computation, for each case. An exit to the boundary of a
copairing, and then the copairing, is the diagram of the copairing at the
case of the exit. An exit past a continuation, and then the continuation, is
that exit. The position of the boundary of an exit is a constructor: the
first position is the nearest continuation, and each other position is an
exit around it. The meaning thus has no search for the part of a list that a
case is in.

A `Free` computation is a well-founded tree, and a loop has no such tree. The
function meaning thus has two more arguments: a number of unrollings, and a
computation for the limit. A loop with no unrolling is the computation for
the limit. A loop with one more unrolling is its body, with the loop at each
exit to the entrance and the remaining computation at each other exit. This
equation holds by computation. Each loop of a diagram has the given number of
unrollings at each of its entrances from the outside, and a loop in the body
of a loop has that number in each iteration. The number of a loop is thus
the same in each place of a diagram. The action of a port map, of a map of
exits, and of a family of diagrams at the exits does not change it, so each
law of the equation sets without feedback holds for each number. A diagram
without a loop does not use the
number. The function meanings at the numbers are finite approximants, as the
thesis gives the meaning of an infinite graph by the limit of its finite
approximants (§2.7.2). The approximants of the thesis count the levels of its
hierarchy, so a loop in a loop has a smaller number there, and they are a
different family.

The specification is the meaning of a diagram with a loop. Its parameter is
a specification of the calls with a runtime: a precondition of a request at
a runtime, and a postcondition on each response. A response of a call is a
response with the next runtime, or a stop. The specification of a diagram is
a dependent polynomial on the interface of the diagram with a runtime, by a
recursion on the diagram. An input is the values of the context and a
runtime. A result is an exit with a runtime, or a stop. A witness of the
precondition has a witness of the precondition of each call that a run can
make. The postcondition at a result is the type of the runs to that result
over the witness, so a run is data.

- The precondition of an exit has no content. A run of an exit is the
  identity of that exit and the result.
- A witness for a step has a witness of the precondition of its call and, for
  each response with its postcondition, a witness for the diagram of that
  response. A run of a step has a response of its call with the
  postcondition. At a stop, the stop is the result. At each other response,
  the run then has a run of the diagram of the response.
- A witness for a composite has a witness for the first diagram and, for
  each run of the first diagram to an exit to the boundary of the
  continuation, a witness for the continuation. A run of a composite has a
  run of the first diagram to a middle result. At an exit to the boundary of
  the continuation, it then has a run of the continuation. At each other
  exit and at a stop, the middle result is the result.
- A copairing has the specification of the diagram of its case. A frame has
  a witness for its diagram and, for each run of that diagram to its exit, a
  witness for the continuation at the case of the bypass, the kept values,
  and that exit.
- The precondition of a loop is an invariant, and a run of a loop is an
  element of the inductive family of
  [Runtime and feedback](#runtime-and-feedback). One iteration has the runs
  of the body at the result that the next entrance, an exit of the loop, or
  a stop names.

The graph of a machine is a specification of the calls, and its precondition
has no content. A specification of the calls with no runtime is the case of
the unit runtime with no stop.

The function meaning is the evaluator of the specification, and the
connection has two halves, for each specification of the calls. A witness of
the precondition of a diagram gives the evidence of the function meaning
with each number of unrollings, when the remaining computation has evidence
at each result of a run. Completeness is the converse: a run of the diagram,
and then a run of the remaining computation, is a run of the function
meaning along that evidence, from a threshold of the number of unrollings.
The two halves are obligations of the stage with feedback.

A verified diagram, for a specification of the interface of the diagram with
a runtime, is a map into the specification of the diagram. At each input
with a witness of the precondition, it has a witness of the precondition of
the diagram, and the postcondition at the result of each run over that
witness. A verified diagram gives the function meaning with each number of
unrollings as an implementation with its verification, when the computation
at the limit has evidence. A bound is second evidence, for a number of
unrollings: each run over the witness reaches the limit of a loop only at a
runtime with a given condition. With the empty condition, the verification
needs no evidence for the computation at the limit.

An operation is pure when its implementation returns without a call. The
`Free` computation of a diagram has one call for each step on a path, in the
order of the steps. After the substitution of the pure implementations, the
computation has
the calls of the effectful operations only, in the order of the runtime wire.
Two orders of the pure calls then give one computation, and the evidence of
each order becomes evidence of that computation.
[Draft/Checks/Order.lean](Draft/Checks/Order.lean) checks this for one
example. That example also constructs the evidence of one order from the
evidence of the other order, through the one computation. The construction
uses a specification of each pure operation that fixes its response. The
statement for each diagram, and the construction of the evidence of an order
for a specification that does not fix the response, are obligations of the
stages that construct diagrams and dependency orders.

The identifications of an equation set are a structural relation with explicit
derivations. Diagrams have no quotient: two presentations of one VSDG
are two diagrams, and a derivation relates them. The diagrams of a step are a
function of the case, and two such functions can agree at each case and be
different functions. Structural agreement relates two diagrams of the same
form whose diagrams agree at each case. Each rule of a derivation relates two
diagrams that agree with the two diagrams of the rule. A port map acts on the
context of a diagram. A map of exits gives a position in a second list to
each boundary of the exits, and it acts on the exits of a diagram. A family
with a diagram for each exit case gives the diagram with those diagrams at
its exits. A composite is the shared form of a continuation, and the first
diagram with that continuation at each exit to its boundary
is the copied form. A frame is the shared form of a diagram, and the
copairing with that diagram for each case of the bypass is the copied form.
The static size of a diagram is the number of its steps. A family has the sum
of the sizes of its cases, and a frame has one count of its diagram. A shared
form thus has a smaller size than its copied form, and the meaning is the
same. The sum needs the list of the cases, so control is finite in the
syntax. The unshared form is held as
the continuations of the meaning. It is not stored data, because its size is
exponential in the number of independent selections.

#### Whole diagrams and interpretation

One type of diagrams has the source diagrams, the realizations, and the
diagrams between them. The signature is its parameter. Each diagram is a
whole routing morphism of the form that the [premises](#premises-and-scope)
give. Each step is an inner box `P i` with its context as the bypass `M i`,
and the sum of the boundaries of the exits is the output of the outer box
`Q`. The diagram of a
frame is in a box whose bypass is the bypass of the frame. The exits and the
composites give a next case and a port map to each case. A bypass acts on a
boundary by the product of polynomials. A composite is a selected
decomposition, and it does not make its components indivisible scheduling
units: the control derivations relate it to the diagram with the continuation
at each exit.

Substitution constructs entry, internal routing, exit maps, and multiplied
bypasses directly from shapes and ports. Its laws include explicit
reassociation of boundaries and of dependent indices. The interpretation of a
wiring is a verified implementation in Aberlé's calculus, and it keeps the
admission and response evidence of each component. Verification is not
recovered by transport across an equality of whole compiled programs.

#### Control wiring, effects, and dependent evidence

**Boundaries as request interfaces.** A typed boundary `p` is evaluated at a
family of value types `V`. The result `⟦p⟧V` is a control case with its port
valuation. A primitive box `P` becomes an Aberlé request interface. Its
request is an input in `⟦P.input⟧V`, and its response is an output in
`⟦P.output⟧V`. A family of boxes also has the box index in the request. A
terminating implementation has the form
`(x : ⟦P.input⟧V) → Free Ops (⟦P.output⟧V)`. Its dependent interface admits the
particular `x` with a supplied witness and specifies the response relative to
that witness.

A box thus has two descriptions by polynomials, and they are different
polynomials. Each boundary is a polynomial of control cases and ports. The box
is a request interface: a shape is an input at the input boundary, and a
position is an output at the output boundary. The first description is for
wiring, and the second is for implementation and verification. Bypass context
is not in the request of the primitive, and evidence of its preservation goes
with it. A specification that mentions the saved context needs a constructed
frame map that relates the context to the witnesses of the primitive. An
arbitrary dependent postcondition does not satisfy a frame rule automatically.

**Effects through the runtime.** The effect signature is interpreted with the
explicit runtime. In the concrete state model, an effectful call consumes
`R × A` and produces `R × B`, and an invariant witness is transformed together
with `R`. Control selection uses the isomorphism

```text
R × (A + B)  ≅  (R × A) + (R × B).
```

Only the selected summand contains the current runtime. Reconvergence returns
the updated resource of the selected branch at a common boundary. A branch tag
is discarded only when the boundary and the specification do not need it.
Reconvergence does not combine simultaneous runtimes. A bypass has the value
carrier `M(V)`, and whiskering carries it past the call with its case, data,
and evidence. The interpretation must respect the polynomial distribution and
reassociation maps. An operad algebra that uses the
control sum gives no interchange law to the value tensor of the runtime.

**Substitution with verification.** The required law compares the
interpretation of a substituted whole diagram with the composition of the
interpretations of its parts. The comparison is constructed along routing and
call constructors, together with the map that consumes the admission and
response witnesses of the components. Erasure agrees with the ordinary
interpretation. A run of the verified composite preserves the runtime
invariant and delivers the specified response evidence. Composition of these
maps must agree structurally with repeated diagram substitution. A proof that
compares only final values cannot supply this dependent law.

**Feedback.** Feedback adds two separate compatibility results. An unchanged
bypass must commute with the control trace, as in Kondyrev–Spivak. A changing
runtime must be threaded around the loop: a body from `R × (A + U)` to
`R × (B + U)` feeds back `R × U` with the latest state and invariant. A bypass
that held `R` unchanged would lose the mutations between iterations. The
loop of the body, the wiring interpretation, and the function with fuel must
agree for their stated observations. Uniformity in the coarse partial-map model does not
preserve a finer distinction between failure and silent divergence, and it
does not supply a dependent invariant map.

#### Runtime and feedback

The runtime wire of a diagram follows control. A runner threads the one
runtime through each selected request. The control case has the runtime and
its invariant witness, and no value port and no bypass holds them. Static
alternatives can name the same resource. The selection of an alternative hands
off the same runtime and its evidence exactly once. The combination of
independent machines in Aberlé's paper does not justify duplication of a
resource that alternatives share.

The concrete state interpretation establishes sequencing, whiskering, pure
centrality, and the required read/write equations pointwise. Arbitrary effects
have no interchange law. Resource contracts state the primitive obligations
and the closure under composition. Lean functions are not intrinsically
linear.

Silent routing with finite control has a constructive resolver that returns
exit, missing-route, or cycle evidence. Its bound comes from finite control,
and it is not an execution cutoff. Closure includes the cycles that
substitution creates.

A loop body is a computation from `A` to `B + A`, with the runtime in `A` and
in `B`. In the specification of a diagram, the precondition of a loop is an
invariant: a family on the entrances, with an initial witness and a witness
of the precondition of the body at each entrance of the family. The body
preserves the family and supplies its witness at each next entrance. The
runs of the loop are the inductive family of runs on entrances equipped with
that evidence: a run exits with the body, or it continues with the body and
then runs from the next entrance. A run is data, and the initial property is
the induction principle of the family. A loop can have an invariant witness
and no terminating run. Its precondition establishes admission of its calls
and preservation of the invariant; it does not require termination. The
diagram-level specification is a D6 construction obligation.

For a body that is a function, a terminating evaluator is a function on an
inductive domain. Domain evidence records that the loop stops from the given
input, and the evaluator recurses on that evidence. Two domain witnesses at
one input are identical, with a proof by induction. A decreasing measure can
construct domain evidence when termination is required by an interpretation.
This evidence is an input to the terminating evaluator, not the general
precondition of an IR loop.

Evaluator fuel bounds a finite unfolding of a diagram. The function meaning
takes a number of loop unrollings and a computation for the cutoff.
Exhausting that budget does not establish divergence or a target failure.
The correspondence with the runs requires soundness and completeness: a
result reached without the cutoff corresponds to a run, and each terminating
run is reproduced at a sufficiently large unfolding bound. No single bound
for all inputs is required. Transformations can change the number of
unrollings needed, so preservation compares runs and their observations,
rather than equal fuel consumption. These diagram-level correspondence
results remain D6 obligations. Neither evaluator fuel nor a target resource
budget is a condition for representing a program in the IR.

A computation without a loop is a function, and it enters the relations
through its graph. The laws of the stages without feedback are pointwise
statements, so the graph carries them.

Returned values, final runtime, visible effects, failure, silent divergence,
and an unfinished finite observation have distinct contracts. Failure is an
exit case of a body. Silent divergence is the absence of a run, and the runs
give no observation of the effects of a loop that does not stop. An evaluator
result without a value is an unfinished finite observation. A partial-map
interpretation that identifies a missing route with divergence is an explicit
coarser observation with a correspondence map. Each trace law names its domain
and observation. Infinite-control trace, infinite observations, and full
coherence stay obligations until they are constructed. No finite test suite
settles them.

### Translation obligations

- The finite, pure, single-result fragment with fixed occurrences is the first
  correspondence milestone. It does not redefine the source language. Its
  coverage statement is for the interchange equation set: each
  dependency-respecting order of the fixed occurrences. It gives no coverage
  for removal, duplication, speculation, or sharing partitions. Each extension
  of the source brings its own equations and preservation obligations.
- Control alternatives must model non-strict selection, reconvergence, and
  dynamically linear state.
- Reuse and tail sharing use source occurrence partitions, with operand and
  result compatibility and the storage-coalescing constraints.
- Loops need initialization, carried values and state, guard, exits, and the
  correspondence with traced feedback. Pipelining adds obligations for
  overlapping iterations.
- The implementation stays polynomial and string-diagrammatic. It does not
  execute the reference semantics of the source as a Petri-net engine.
- A translation from a VSDG selects an order for the operations that no wire
  connects, a case for each operation, and the continuations that two paths
  share. For two operations of which one is pure, centrality makes the order
  irrelevant. For an operation that is named for discard naturality, position
  invariance makes the case irrelevant. For a continuation, the control
  equation set makes the shared form and the copied form one meaning. A
  generator of realizations does not use a case as a scheduling unit.
