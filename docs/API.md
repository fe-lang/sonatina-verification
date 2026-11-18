# Prelude overview

[Library overview](../README.md)

The Prelude is a constructive Lean 4 library for work on polynomial
interfaces. `import Prelude` supplies the foundations; its declarations have no
axiom dependencies. Optional axiom-backed APIs require a separate
`import Prelude.Axiom` or `import Prelude.Eq`.

The documentation of each declaration is its documentation comment in the
source. The documentation comment at the start of each module gives the
concepts of that module, with its examples, its implementation notes, and its
references.

## Use

```lean
import Prelude

open Prelude
open scoped Prelude

def reindex {n m : Nat} (p : n ≡ m) (i : Fin n) : Fin m :=
  Identity.transport Fin p i

def compareIndices (n m : Nat) : Dec (n ≡ m) := decideEq n m

example {n m : Nat} (p : n ≡ m) : n = m := p.toEq
```

`open scoped Prelude` enables the identity notation `a ≡ b`.

Ordinary data and effect interfaces are Lean's: `Empty`, `Unit`, `Bool`, `Nat`,
`Int`, `Fin`, `List`, `Vector`, `Option`, `Except`, `Prod`, `Sum`, `Sigma`,
`Functor`, `Applicative`, and `Monad`. Function composition uses `∘`.
Lean's `WellFounded` and termination machinery remain available alongside the
Prelude's Type-valued relations. `PLift p` embeds a proposition as a type;
`Nonempty A` expresses inhabitation of a type as a proposition.

## Modules

The Prelude imports Lean's `Init` and supplies the following modules:

| Module | Contents |
| --- | --- |
| [`Prelude.Identity`](../Prelude/Identity.lean) | The identity type `a ≡ b` in `Type`, with path induction, transport, congruence, and the laws of identities; identities of dependent pairs; constructor facts for `Option` and `Sum`; isomorphisms (`Iso`), identities of functions at each argument (`Homotopy`), the contractible types, and the propositions |
| [`Prelude.Decision`](../Prelude/Decision.lean) | Decisions with a witness or a refutation (`Dec`), their combinators, and decidable identity (`DecEq`) with instances by structural recursion |
| [`Prelude.Indexed`](../Prelude/Indexed.lean) | The positions of an element in a list (`Elem`) and the environments with one value for each element (`All`), with lookup, update at a position, mapping, concatenation, tabulation, and selection, and their laws |
| [`Prelude.Relation`](../Prelude/Relation.lean) | The paths of a relation (`Steps`), accessibility in `Type`, computations as relations (`Rel`), and loops (`Loop`) with the initial property, the laws, the domain evidence, and the function with fuel |
| [`Prelude.Container`](../Prelude/Container.lean) | The import of the nine container modules |
| [`Prelude.Container.Core`](../Prelude/Container/Core.lean) | Containers with shapes and positions, polynomial extensions, and morphisms; constants, identity, sums, family sums, products, and composition |
| [`Prelude.Container.Agreement`](../Prelude/Container/Agreement.lean) | Agreement of extensions and of morphisms, and the agreement of the two layers of a composite |
| [`Prelude.Container.Comonoid`](../Prelude/Container/Comonoid.lean) | Comonoids for composition with their homomorphisms, the state object with its comonoid, and lawful lenses |
| [`Prelude.Container.Section`](../Prelude/Container/Section.lean) | Closed providers, specifications of an interface with their maps, and the evidence that a provider satisfies a specification |
| [`Prelude.Container.Free`](../Prelude/Container/Free.lean) | Computations on an interface and implementations of one interface by calls to another, with agreement, congruences, and the laws of bind, substitution, composition, and interpretation |
| [`Prelude.Container.Verified`](../Prelude/Container/Verified.lean) | The evidence that a computation satisfies a specification, lifts of implementations and verified implementations, the runs of a computation along its evidence, and the specification of an implementation from a specification of its calls |
| [`Prelude.Container.Commute`](../Prelude/Container/Commute.lean) | The calls that commute in a congruence of computations, the central calls, and the copyable calls |
| [`Prelude.Container.Runtime`](../Prelude/Container/Runtime.lean) | The interface with a runtime, machines, the computation and the implementation with a runtime at each call, specifications with an invariant of the runtime, machines along a lens of runtimes, and the cell with the five equations of global state |
| [`Prelude.Container.Indexed`](../Prelude/Container/Indexed.lean) | Indexed containers with typed extensions, morphisms that preserve the input indices, and indexed composition |

The container modules import only the Prelude foundation.

Two modules are separate imports. `import Prelude` does not include them.

| Module | Contents |
| --- | --- |
| [`Prelude.Eq`](../Prelude/Eq.lean) | Adapters between Lean's `Prop` equality and the identity type, and between `DecidableEq` and `DecEq`. An identity from a Lean equality reduces only when its endpoints are definitionally equal. |
| [`Prelude.Axiom`](../Prelude/Axiom.lean) | Function extensionality from Lean's axiom, with its `Quot.sound` dependency. Its result does not reduce. |

## Conventions

- `a ≡ b` is the identity type in `Type`, with the constructor `Identity.refl`.
  Lean's `=`, `==`, and identity monad `Id` retain their standard meanings.
- Proofs inhabiting `Identity` are definitions (`def`); Lean's `theorem` command
  is reserved for propositions.
- Identities, agreements, and decisions are data in `Type`, and they compute by
  identity elimination.
- An extension and a computation contain functions, so each of their laws
  holds up to identity or up to an agreement. An agreement of two extensions
  has an identity of the shapes and an identity of the values at each
  position. An agreement of two computations has the same call and an
  agreement of the continuations at each response.
- `f.trans g` is composition in traversal order: first `f`, then `g`.
- Shapes, positions, and values have independent universe levels.

## Build and checks

```sh
lake build
```

`lake build` checks the Prelude and its tests. The tests have six modules.
[`PreludeTests.Prelude`](../PreludeTests/Prelude.lean) covers universe levels,
dependent transport, kernel reduction of equality decisions, and indexed
environments.
[`PreludeTests.Relation`](../PreludeTests/Relation.lean) checks distinct
execution traces, accessibility recursion, and loops: a run with an arbitrary
initial state, its domain evidence and fuel, the round trips of the loop
laws, evidence that depends on the run across unrolling, and a loop with the
state in `Type` and the result in `Type 1`.
[`PreludeTests.Eq`](../PreludeTests/Eq.lean) and
[`PreludeTests.Axiom`](../PreludeTests/Axiom.lean) check the separate modules.
[`PreludeTests.Runtime`](../PreludeTests/Runtime.lean) checks machines: a state
invariant, a specification of two runtimes for one program, the laws of the
run for a bind, a substitution, and a composite, evidence that moves along the
laws of a bind and of a substitution, the two general lifts of an
implementation with a runtime, and the congruence of a machine. They check a
lawful lens of runtimes with its three laws, the composite of two lenses, the
run of a machine along a lens, and two computations of a cell that have one
run on a cell of pairs.
[`PreludeTests.Container`](../PreludeTests/Container.lean) checks container
universes, position selection and sharing, polynomial composition, the round
trips of `sumIso` and `compIso`, the value witnesses of composed agreements, a
family sum and a computation with shapes in `Type 1`, heterogeneous typed
references, rejection of ill-typed ports, and morphisms with non-definitional
index equality.
