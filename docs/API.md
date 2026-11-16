# API reference

[Library overview](../README.md)

This reference describes the Prelude.
`import Prelude` supplies the foundations; its declarations have no
axiom dependencies. Optional axiom-backed APIs require a separate
`import Prelude.Axiom` or `import Prelude.Eq`.

## Prelude

```lean
import Prelude

open Prelude
open scoped Prelude

def reindex {n m : Nat} (p : n ≡ m) (i : Fin n) : Fin m :=
  Identity.transport Fin p i

def compareIndices (n m : Nat) : Dec (n ≡ m) := decideEq n m

example {n m : Nat} (p : n ≡ m) : n = m := p.toEq
```

The Prelude imports Lean's `Init` and supplies the following modules:

| Module | Contents |
| --- | --- |
| [`Prelude.Identity`](../Prelude/Identity.lean) | Internal identity, path induction, transport, congruence, identity laws, dependent pair identities, constructor facts for `Option` and `Sum`, and `toEq`; `Iso` with its transport of dependent evidence; `Homotopy` with `refl`, `symm`, and `trans` |
| [`Prelude.Decision`](../Prelude/Decision.lean) | `Refute`, `Dec`, `DecEq`, `decideEq`, decision combinators, and structural `DecEq` instances |
| [`Prelude.Indexed`](../Prelude/Indexed.lean) | `Elem` positions and `All` dependent environments over `List`, with lookup, update at a position, mapping, concatenation, tabulation, the positions of a concatenation, and selection, with their laws |
| [`Prelude.Relation`](../Prelude/Relation.lean) | `Steps` with composition, mapping, and length; `Accessible` and `TypeWellFounded` for Type-valued relations; `Rel` computations with graph, composition, copairing, and agreement; `Loop` with its initial property, laws, domain evidence, and function with fuel |
| [`Prelude.Container`](../Prelude/Container.lean) | The import of the six container modules |
| [`Prelude.Container.Core`](../Prelude/Container/Core.lean) | Shapes and positions, polynomial extensions, lawful mapping, morphisms, constants, identity, sums, family sums, products, and composition |
| [`Prelude.Container.Agreement`](../Prelude/Container/Agreement.lean) | Extension and morphism agreement with their congruence laws |
| [`Prelude.Container.Section`](../Prelude/Container/Section.lean) | Closed providers, morphism interpretation, specifications, witness-dependent evidence, and computational reindexing laws |
| [`Prelude.Container.Free`](../Prelude/Container/Free.lean) | `Free` computations with bind, interpretation, and structural agreement; implementations with substitution, composition, and copairing; the laws of the two |
| [`Prelude.Container.Verified`](../Prelude/Container/Verified.lean) | `FreeDep` evidence that a computation satisfies a specification, with bind, substitution, interpretation, and transport along agreement; `ImplDep` lifts of implementations with composition and copairing; the laws of interpretation |
| [`Prelude.Container.Runtime`](../Prelude/Container/Runtime.lean) | The interface with a runtime (`Container.runtime`), machines as its closed providers (`Machine`), the computation and the implementation with a runtime at each call (`Free.thread`, `Impl.thread`), the run on a machine and the machine of an implementation (`Machine.run`, `Machine.impl`), the graph of a machine with its evidence, and the specification with an invariant of the runtime with the move of evidence to it (`DepPoly.invariant`, `FreeDep.thread`) |
| [`Prelude.Container.Indexed`](../Prelude/Container/Indexed.lean) | Input/output indexed containers, typed extensions, index-preserving morphisms, and indexed composition |

Ordinary data and effect interfaces are Lean's: `Empty`, `Unit`, `Bool`, `Nat`,
`Int`, `Fin`, `List`, `Vector`, `Option`, `Except`, `Prod`, `Sum`, `Sigma`,
`Functor`, `Applicative`, and `Monad`. Function composition uses `∘`.
Lean's `WellFounded` and termination machinery remain available alongside the
Prelude's Type-valued relations. `PLift p` embeds a proposition as a type;
`Nonempty A` expresses inhabitation of a type as a proposition.

### Identity and evidence

For `A : Type u`, the inductive family `Identity (a : A) (b : A)` lives in
`Type u`, with constructor `Identity.refl`. The scoped notation is `a ≡ b`.
Lean's `=`, `==`, and identity monad `Id` retain their standard meanings.
Proofs inhabiting `Identity` are definitions (`def`); Lean's `theorem` command
is reserved for propositions.

`Identity.ind` supports motives depending on the identity witness.
`Identity.transport` accepts families in any `Sort`, including `Prop`.
`Identity.trans p q` traverses `p` followed by `q`; the `Trans` instance supports
`calc` blocks. `Identity.sigma` combines a base identity with an identity in
the transported fiber.

`Identity.toEq` supplies Lean equality premises from internal evidence.

`Iso A B` has a map in each direction and the two round-trip identities,
`invTo` and `toInv`. For a family `Q` on `A`, `Iso.across` moves evidence at
`x` to the family `Iso.Moved Q` at `e.to x`, and `Iso.back` returns it.
`Iso.backAcross` and `Iso.acrossBack` are the round trips of the evidence.
`Identity.inlFiber` and `Identity.inrFiber` show that two identities from one
element of a sum to values of one constructor are one identity.

`Dec.yes` contains a witness; `Dec.no` contains a function to `Empty`.
`DecEq` instances for `Unit`, `Bool`, `Nat`, `Fin n`, `Option`, `Sum`, `Prod`,
and `List` are defined by structural recursion, and their witnesses reduce in
the kernel. The `Nat` instance is unary: its cost is linear in the smaller
argument. `Dec.toDecidable` decides `Nonempty A`; it does not extract witnesses
from arbitrary Prop-valued existence proofs.

Two modules are separate imports. `import Prelude` does not include them.

| Module | Contents |
| --- | --- |
| [`Prelude.Eq`](../Prelude/Eq.lean) | `Identity.ofEq` lifts a Lean equality to an identity, with the round trips `ofEqToEq` and `toEq_ofEq`. `Identity.unique` follows from Lean's proof irrelevance. An existing `DecidableEq A` supplies a low-priority `DecEq A` instance; `DecEq.toDecidableEq` is the reverse adapter. An identity from `ofEq` reduces only when its endpoints are definitionally equal. |
| [`Prelude.Axiom`](../Prelude/Axiom.lean) | `Axiom.funext`, which inherits Lean's function extensionality and its `Quot.sound` dependency. Its result does not reduce. |

`Elem` retains occurrence information, including repeated elements of a list.
`All P xs` contains a `P x` at every position of `xs`.
`Elem.left` and `Elem.right xs` are the positions of the two parts of
`xs ++ ys`. `Elem.consCases` is the case analysis of a position of a nonempty
list, and `Elem.ofNil` gives a value of each type from a position of the
empty list. `All.select env positions` gives the values of `env` at a list of
positions, which can repeat a position and omit a position.
`All.head`, `All.tail`, and `All.consCases` are the first value, the other
values, and the case analysis of an environment of a nonempty list.
`All.lookupLeft` and `All.lookupRight` give the value at a position of each
part of a concatenation, and `All.lookupMap` gives the value of a map at a
position. `All.mapCongr`, `All.mapMap`, and `All.mapAppend` are
the laws of `All.map`. `All.selectAppend` gives the selection at a
concatenation of two lists of positions. `All.selectTabulate` gives the
selection at a table of positions, from the value at each position of the
table. `All.selectSelect` gives the selection at selected positions. The
functions on `Elem` and `All` use `casesOn` with an explicit motive, so their
evaluation eliminates no equality of lists.
`Steps R a b` retains the individual transitions, so executions with equal
endpoints can have different lengths and labels. `Steps.foldProp` interprets
such a trace in a reflexive, transitive Prop-valued relation.

### Computations and loops

`Rel A B` is `A → B → Type r` for `A : Type u` and `B : Type v`. An element of
`F a b` is a run of the computation `F` from the input `a` with the result
`b`. Inputs, results, and runs have independent universe levels.
`Rel.graph f` is the graph of a function, `Rel.seq` is composition in
traversal order, and `Rel.copair` is the map out of a sum.
`Rel.Agreement F G` is an `Iso` of the run families at each input and result.
`Rel.copair` and `Rel.onExit` use `ULift` on the runs of each case to give the
cases one level. `Rel.lift F` has the runs of `F` at a higher level.
`Rel.graphSeq f G` is the agreement of `Rel.graph f ; G` with the computation
`G` at the value of `f`, with the runs of the graph at each level.

`Loop F` is the loop of a body `F : Rel A (B ⊕ A)`. A run is `Loop.exit` with
an exit run of the body, or `Loop.next` with a continue run of the body and
the run from the next input. The level of the runs of `Loop F` is the maximum
of the levels of the inputs, the results, and the runs of `F`.

| Declaration | Statement |
| --- | --- |
| `Loop.elim`, `Loop.elimUnique` | The initial property: the map from the loop to a family that the two rules close, and its uniqueness at each run |
| `Loop.path` | Agreement with the paths of continue steps that end with an exit step, through `Steps` |
| `Loop.fixpoint` | Agreement of `Loop F` with `F ; [id, Loop F]` |
| `Loop.unrolling` | Agreement of `Loop F` with the loop of `Rel.twice F`, the body run twice |
| `Loop.strengthTo`, `Loop.strengthFrom`, `Loop.strengthToFrom` | The maps for a body beside an unchanged context (`Rel.withContext`), and one round trip |
| `Loop.naturalTo`, `Loop.naturalFrom` | The maps between the loop of `F ; (K + id)` (`Rel.onExit`) and `Loop F ; K` |
| `Loop.uniformTo`, `Loop.uniformFrom` | The maps between the loops of two bodies that a function relates |
| `Loop.codiagonalTo`, `Loop.codiagonalFrom` | The maps between the loop of a merged body (`Rel.merged`) and the loop of the inner loop |

For a function body `f : A → B ⊕ A`:

| Declaration | Statement |
| --- | --- |
| `Loop.Domain f a` | Evidence that the loop stops from `a` |
| `Loop.Domain.eval`, `Loop.Domain.run` | The result by recursion on the evidence, and its run in `Loop (Rel.graph f)` |
| `Loop.Domain.unique` | Two domain witnesses at one input are identical |
| `Loop.Domain.ofMeasure`, `Loop.Domain.ofAccessible` | Evidence from a decreasing `Nat` measure, and from `Accessible` for the continue steps |
| `Loop.domain`, `Loop.domainEval` | The evidence from a run, and the identity of its result with the result of the run |
| `Loop.resultUnique` | Two runs from one input have one result |
| `Loop.fuel`, `Loop.fuelSound`, `Loop.fuelComplete` | The loop with at most `n` runs of the body. A result has a run, and a run gives its result at the fuel `r.length`. |

### Containers

`Container` has fields `Shape : Type s` and `Pos : Shape → Type p`.
Its extension `C.Ext A` is `(s : C.Shape) × (C.Pos s → A)`.
Shapes, positions, and labels have independent universe levels. Positions can
carry values or references; multiple positions can carry the same reference.

`Hom.Agreement` compares each shape and backward position map through
`Ext.Agreement`. `Hom.transCongr` and `Hom.Agreement.apply` preserve this evidence
under composition and value action. `Container.Section` describes a closed
provider. `Container.DepPoly C` is a specification of `C`: `Pre` is a
precondition on each shape, and `Post` is a postcondition on each response that
depends on the witness of the precondition. `DepPoly.sigma r` is the
specification of `Container.sigma F` that has `r i` at each index.
`Container.Evidence r provider` is the evidence that a closed provider satisfies
`r`. `Evidence.reindex` transports response evidence while retaining the exact
input and supplied precondition witness. `Container.zero` is the polynomial
with no shape. `Section.zero` is its closed provider, `DepPoly.zero` is a
specification of it, and `Evidence.zero r` is the evidence of each of its
specifications. An implementation into `Container.zero` makes no call.

```lean
import Prelude

open Prelude
open scoped Prelude

abbrev binary : Container where
  Shape := Unit
  Pos _ := Fin 2

def operands : binary.Ext Nat := ⟨(), fun _ => 3⟩

example : (binary.map (fun n => n + 1) operands).2 ⟨0, by decide⟩ ≡ 4 := .refl
```

An `abbrev` signature exposes its shape and position types to Lean's instance
search. `C.map` supports maps between different universes; `Functor C.Ext` and
`LawfulFunctor C.Ext` supply Lean's standard mapping interface. `mapId` and
`mapComp` express the laws using internal identity. `Ext.Agreement` has a
shape identity and pointwise value identities, and `Ext.Agreement.ind` is its
eliminator. Agreement is reflexive, symmetric, and transitive, and mapping
preserves it. `Ext.All`
assigns Type-valued evidence to every position; `Agreement.all` transports that
evidence using the supplied shape and value witnesses.

`Container.Hom C D` contains `shape : C.Shape → D.Shape` and
`position : (s : C.Shape) → D.Pos (shape s) → C.Pos s`.
`Hom.apply` interprets it on extensions. Position maps can select, repeat, or
reorder source positions. `f.trans g` applies `f` followed by `g`; `idTrans`,
`transId`, `transAssoc`, `applyId`, `applyTrans`, and `natural` give its laws.

| Construction | Equivalent extension | Conversion API |
| --- | --- | --- |
| `Container.const A` | A shape in `A`, with no positions | Shape projection |
| `Container.identity` | One labelled position | Value at `()` |
| `C.sum D` | `Sum (C.Ext A) (D.Ext A)` | `sumIn`, `sumOut`, `sumIso` |
| `C.product D` | `C.Ext A × D.Ext A` | `productIn`, `productOut` |
| `C.comp D` | `C.Ext (D.Ext A)` | `flatten`, `unflatten`, `compIso` |

`sumIso` and `compIso` are `Iso` values: their fields `invTo` and `toInv` are
the round-trip identities of the sum and composition conversions.
For products, `productOutIn` gives internal identity and `productInOut` gives
`Ext.Agreement`, with an identity at each left or right position.
`flattenMap` relates mapping through composition to mapping both layers.
Sums use `ULift` on positions to accommodate different position universes;
`sumIn` and `sumOut` handle these lifts.

`Container.sigma F` is the sum of a family `F : ι → Container`. A shape is an
index with a shape of the container at that index, and the index type has its
own universe level. `Hom.inj F i` is the inclusion of one member, and
`Hom.copair f` is the morphism out of the sum that has `f i` at each index.
`Hom.injCopair` and `Hom.copairInj` are the two equations of the coproduct, and
each holds by `.refl`.

### Computations and implementations

`Free C α` is a computation that returns an `α` after a well-founded sequence of
calls to `C`. Its constructors are `pure value` and `request shape next`, where
`next` continues at each response. Shapes, positions, and values have
independent universe levels.

| Definition | Meaning |
| --- | --- |
| `Free.call a` | One call that returns its response |
| `x.bind f`, `Free.map f x` | Continue each returned value; relabel the returned value |
| `Free.run provider x` | Interpret each call by a closed provider `Section C` |
| `Impl C D` | An implementation of `C` by calls to `D`: `(a : C.Shape) → Free D (C.Pos a)` |
| `Free.subst g x` | Replace each call with its implementation |
| `Impl.id C`, `f.trans g` | The implementation with one call; composition in traversal order |
| `Impl.run f provider` | The closed provider of `C` from a closed provider of `D` |
| `Impl.copair f` | The implementation of `Container.sigma F` from an implementation at each index |
| `Hom.toImpl f` | The implementation with one call at each shape |
| `Impl.ofSection f` | The implementation that returns the response of a closed provider without a call. An operation with such an implementation is pure. |
| `Impl.Returns f a` | The implementation of the shape `a` returns without a call: a response, and the agreement of `f a` with the computation that returns it. `Returns.bind` gives that response to a continuation. |

A computation has functions as continuations. `Free.Agreement x y` is thus the
relation of the laws: equal returned values, and the same call with agreement
of the continuations at each response. It is reflexive, symmetric, and
transitive. Transitivity eliminates its first agreement, and
`Agreement.before` of its second agreement takes the first computation.
`Agreement.bind`, `Agreement.subst`, and `Agreement.run` are the
congruences: `Agreement.run` gives an identity of the returned values from
agreeing providers. `Impl.Agreement f g` is agreement at each shape.

| Law | Statement |
| --- | --- |
| `pureBind`, `bindPure`, `bindAssoc` | The monad laws of `bind`; the first holds by `.refl` |
| `substBind`, `substId`, `substTrans` | Substitution preserves `bind`; substitution of `Impl.id`; two substitutions are one substitution of the composite |
| `Impl.idTrans`, `Impl.transId`, `Impl.transAssoc`, `Impl.transCongr` | Identity, associativity, and congruence of composition |
| `runBind`, `runSubst`, `Impl.runTrans`, `Impl.runCongr` | Interpretation of `bind`, of substitution, and of composition, as identities of returned values |
| `Impl.ofSectionRun`, `Free.substOfSection` | A pure implementation gives its provider; a computation whose calls are all pure agrees with the value of its run |
| `Hom.toImplId`, `Hom.toImplTrans`, `Hom.toImplRun` | `Hom.toImpl` preserves identity, composition, and interpretation; each holds by `.refl` |

### Verified computations

`FreeDep r Q x` is the evidence that the computation `x` satisfies the
specification `r` of its interface and gives `Q` at each returned value. Its
constructors follow the constructors of `x`. `pure result` has the evidence at
a returned value. `request pre verified` has a witness of the precondition of a
call, and `verified` continues at each response with the evidence of its
postcondition for that witness. The universe levels of the specification and of
`Q` are independent.

| Definition | Meaning |
| --- | --- |
| `FreeDep.call a pre` | One call with a witness of its precondition; the response has the evidence of its postcondition |
| `h.bind k` | Continue each returned value with a verified computation that receives the evidence at that value |
| `h.run e` | The evidence at the value that `x.run provider` returns, for `e : Evidence r provider` |
| `h.reindex agree` | The evidence of `y` from the evidence of `x` and `agree : Free.Agreement x y` |
| `h.result`, `h.parts` | The evidence at a returned value; the precondition witness of a call with the evidence of its continuation |
| `ImplDep r t f` | The lift of `f : Impl C D`: for each shape and each witness of its precondition in `r`, evidence that `f a` gives the postcondition, with `t` as the assumption on the calls |
| `h.subst gg` | Replace each call with its verified implementation; the evidence of `x.subst g` |
| `ImplDep.id r`, `ff.trans gg` | The lift of `Impl.id`; the lift of `f.trans g` |
| `ImplDep.copair ff` | The lift of `Impl.copair f` for `DepPoly.sigma r`, from a lift at each index |
| `ff.run e` | The evidence of the provider `f.run provider`, for `e : Evidence t provider` |
| `ff.reindex agree` | The lift of `g` from the lift of `f` and `agree : Impl.Agreement f g` |
| `ImplDep.ofEvidence e` | The lift of `Impl.ofSection f`, for `e : Evidence r f` |

An implementation with its lift is a verified implementation. The lift is
indexed by the implementation, so the lift of a composite is a lift of the
composite of the implementations. `ff.trans (ImplDep.copair gg)` is Aberlé's
`compDep`.

| Law | Statement |
| --- | --- |
| `FreeDep.runBind` | The run of a bind gives the evidence of the run of the continuation, across the identity `Free.runBind` |
| `FreeDep.runReindex` | The run of moved evidence is the evidence of the first run, across the identity that `Agreement.run` gives |
| `FreeDep.runSubst` | The run of substituted evidence is the run of the evidence with the provider of the implementation, across the identity `Free.runSubst` |
| `ImplDep.runTrans` | The evidence of a composite is the evidence of its two stages, across the homotopy `Impl.runTrans` |

`IndexedContainer I O` has `Shape : O → Type s`, positions at each shape,
and `index : (s : Shape o) → Pos s → I`. Its extension is
`C.Ext X o = (s : C.Shape o) × ((p : C.Pos s) → X (C.index s p))`.
The input index determines the type of the value at each position:

```lean
def resolve {Ty : Type} {Γ : List Ty} {V : Ty → Type}
    (C : IndexedContainer Ty Ty) (env : All V Γ) {o : Ty}
    (node : C.Ext (fun t => Elem t Γ) o) : C.Ext V o :=
  C.map (fun _ ref => env.lookup ref) node
```

Indexed `Hom` additionally carries Type-valued `index` witnesses. Its `apply`
transports each value along the corresponding witness. `Hom.Agreement` relates
shapes and positions and supplies an identity between the composed index
witnesses. The unit and associativity laws construct this agreement.
`Agreement.apply`, `natural`, and `applyTrans` give `Ext.Agreement` of typed
values, and `Ext.Agreement.all` transports positionwise dependent evidence.
For `C : IndexedContainer J O` and `D : IndexedContainer I J`,
`C.comp D : IndexedContainer I O` has conversions between its extension and
`C.Ext (D.Ext X)`. Indexed `identity`, `const`, and `Ext.All` are also available.
`C.toContainer o` forgets the input indices at an output;
`Container.indexed` views an ordinary container as indexed by `Unit`.

Container identities and agreement witnesses live in `Type` and compute by
identity elimination. The container modules import only the Prelude foundation.

## Build and checks

```sh
lake build
```

`lake build` checks the Prelude and its tests. The tests have five modules.
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
invariant, and a specification of two runtimes for one program.
[`PreludeTests.Container`](../PreludeTests/Container.lean) checks container
universes, position selection and sharing, polynomial composition, the round
trips of `sumIso` and `compIso`, the value witnesses of composed agreements, a
family sum and a computation with shapes in `Type 1`, heterogeneous typed
references, rejection of ill-typed ports, and morphisms with non-definitional
index equality.
