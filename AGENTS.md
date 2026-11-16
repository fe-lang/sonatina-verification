# Compiler project instructions

[CONCEPT.md](CONCEPT.md) fixes the premises and defines the design and the
source correspondences; [PLAN.md](PLAN.md) defines the modules and stages and
tracks their status. Read the relevant sections and mathematical source
definitions before implementing a constructor family. `Draft.*` is the
implementation. [NOTES.md](NOTES.md) holds the research observations and
source contracts that the stages must establish.

## Constructivity is mandatory

**The compiler implementation is constructive: each of its declarations
depends on no axiom through its whole dependency closure, and its evidence
computes.** The implementation is the whole IR implementation: the dependent
polynomial constructions that follow Aberlé's methods, and each correctness
proof that a construction uses as data to compute. `Prelude` and `Draft` are
the implementation. Two tests decide the rule. A declaration that fails a test
blocks its dependents: stop at an unresolved obligation, and do not build on a
placeholder.

1. **No axiom.** No declaration, generated and private helpers included,
   depends on an axiom or is `unsafe`, `partial`, `opaque`, or
   `noncomputable`. Thus `sorry`, `native_decide`, `funext`, `propext`,
   `Quot.sound`, and `Classical.choice` are not available. Prelude has no
   exemption. A check module ends with `#guard_msgs in #print axioms` for its
   checks. The build fails when a check, or a construction that the check
   consumes, depends on an axiom.
2. **Computation.** A kernel check eliminates the actual witness and closes by
   `.refl`, with arbitrary values where possible. Freedom from axioms does not
   show that evidence computes: an identity that passes through `Prop` has no
   axiom and can fail to reduce.

   A check that is too deep for the elaborator has closed inputs and closes by
   `decide +kernel`: only the kernel reduces the two sides. Such a check
   measures cost only. The kernel reduces a transport along a `Prop` equality
   when the two ends are equal by computation, so closed inputs can hide
   evidence that does not reduce for general inputs. A `.refl` check of the
   same construction with arbitrary values goes with it.

The tests apply to the declarations, and not to the tools that make them.
Tactics, the elaborator, and scripts use Lean's library, which depends on
axioms. The term that a tool produces is what the tests check. The matchers
that Lean generates for pattern matching on an indexed family contain
eliminators of `Eq` and `HEq`. They are acceptable when the two tests pass.

Two rules need judgment, because the tests do not decide them:

- **Evidence stays in `Type`.** Evidence that a later construction consumes is
  data. Do not put it in `Prop`, in `Nonempty`, or in an existential
  proposition, and do not use proof irrelevance in place of a computation.
  `Prop` is for side conditions that no construction eliminates into data,
  such as bounds and decidable conditions.
- **No axiom as a premise.** Extensionality or choice that enters as a
  parameter, a class instance, a quotient, or an opaque constant has the
  effect of the axiom. An interface premise needs a constructive instance.

An observational proof of correctness is not under the rule. It states a
property of the compiler for metatheoretical verification, and no construction
uses it as data to compute. It can use axioms, `Prop`, and libraries that
depend on axioms. The condition is the direction of dependency: an
observational proof can import the implementation, and nothing in `Prelude` or
`Draft` depends on an observational proof.

Imports make the boundary:

- `Draft` loads only modules of `Init`, `Prelude`, and `Draft`.
- Observational proofs, and the code that only they use, are in modules
  outside that closure:
  - `Observations.*` has the observational proofs about the compiler.
  - `Prelude.Eq` converts Lean's `Prop` equality into Type-valued identity,
    for boundaries with libraries that state results in `Prop`.
  - `Prelude.Axiom` has function extensionality for observational proofs.
- Evidence that `Prelude` or `Draft` consumes cannot move into one of these
  modules. An exception needs the user's decision.

## Construction method

Foundational types, operations, and reusable laws belong in Prelude. Inspect and
reuse its existing APIs before introducing a definition. Extend or improve the
owning Prelude module when functionality is missing; do not duplicate it in
Draft, introduce parallel foundational types, or add wrappers that merely rename
the same functionality. Draft contains compiler-specific constructions,
experiments, and checks.

The implementation is correct by construction, with Aberlé's method. The
compiler is built in her category of specifications. An object is an
interface with its specification, a `DepPoly`. A morphism is an
implementation with its verification. The forgetful functor to her category
of interfaces gives the plain interface and the plain implementation:

- An operation has its specification as a part of its signature.
- A verified computation is a computation with its `FreeDep`. A diagram is an
  implementation of its own interface by calls of the interface of its
  signature, and a verified diagram is that implementation with its
  verification. A step takes the witness of the precondition of its operation
  from the context that the diagram holds, and its continuation receives the
  postcondition of the response.
- A verified implementation is an implementation with its `ImplDep`. A
  lowering is a verified implementation. A pass maps a verified object to a
  verified object of the same specification. An agreement of the plain
  computations is the plain part of a pass, and the evidence moves along it.

Composition (`ImplDep.trans`, `ImplDep.copair`) keeps correctness. A
construction and its verification are built in the same manner, and no stage
is complete with the plain part only. Before a new structure, test if it is a
`DepPoly` on a container, a `FreeDep`, or an `ImplDep`, and use that form. Use
inductive data, recursion, and computational Type-valued identity. Retain the
supplied precondition witness and witness-dependent postconditions.

Build routing directly from shapes and backward port maps. Use pointwise
agreement and structural relations, with explicit composition, congruence,
reindexing, and dependent consumer maps; never assume consumers respect a
relation. Exercise a complete dependent example before extending the library.

The IR is one string-diagrammatic syntax. Polynomials formalize it, and its
effects have the premonoidal structure. Preserve the whole diagram. The runtime
wire is linear: no construction copies it or discards it, and no rewrite
changes the order of two effects without an effect law. Do not implement VSDG
Petri-net execution. Selection is the copairing of the control sum: do not add
a selection operation, and do not use a case or a nested region as a
scheduling unit. Preserve source coverage, admissible
choices, specifications, laws, and observations; representation changes
require constructive correspondence.

## Verification

Before building dependent layers:

1. Write named kernel checks that consume the actual Type-valued evidence
   through branching, repeated substitution, and witness-dependent
   postconditions, with arbitrary witness/state parameters where possible. Add
   functional tests for observations.
2. End each check module with `#guard_msgs in #print axioms` for its checks,
   and run `lake build`. A module that `import Draft` does not load is not
   built, so `Draft.lean` imports each module.

Each kernel check in `Draft` sets `smartUnfolding false`. With the default, the
elaborator reduces the recursion argument of a recursive function again at each
call, and the time of a nested run grows by a constant factor for each level.
The option is for one declaration (`set_option smartUnfolding false in`) or
for a module. A module that defines diagrams sets it for each check only. With
the option, the elaborator writes an implicit argument that it computes, such
as the context of a port, in recursor form, and the code generator rejects the
definition.

A check that exceeds Lean's default limits has a cause in a construction. Find
the cause. Never disable kernel checking or raise a resource limit for
acceptance. `python3 scripts/profile_lean.py PATH.lean` gives the elaboration
time and the kernel time of one module.

Unresolved proofs and failed computation checks block dependents. Compiled
execution is not a kernel proof.

## Working method

A failed check has a cause in a construction. Correct that construction. When
the cause is a representation decision, change the representation and its
consumers together; do not repair declarations one at a time.

Do not add process. No audit reports, inventories, classification documents,
status trackers, or tools whose output is a report. A check is a command that
fails. Documents state the design and the status of each stage.

Report a number only from a command run in the same session.

Do not add rules to this file or to CONCEPT without the user's instruction, and
do not cite a self-written restriction as a constraint. When a rule seems to
force a poor design, tell the user.

## Writing

Write final-state artifacts without conversational or development history.
