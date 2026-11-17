# Sonatina v2 design proposal

This repository contains the design of a proposed architecutre for Sonatina v2
formalized in Lean 4. The proposed architecture is a continuation of the
research pursued in _FY24-1818: Enhancing Security, Efficiency, and Robustness
of Sonatina IR Design through Formal Verification_ research grant awarded by
the Ethereum Foundation in Q4 2024.

The proposal revisits Value State Dependence Graphs (VSDGs) through polynomial
interfaces and premonoidal string diagrams. Its central problem is
sequentialization: turning program dependencies into efficient executable code
by choosing operation order, control flow, sharing, duplication, and storage.

Programs are represented as typed open diagrams. Polynomial boundaries describe
control alternatives and the values available in each alternative. Wiring
routes, copies, and discards values, while a linear runtime wire preserves
effect dependencies. Explicit transformation laws relate different realizations
of the same computation.

The working hypothesis is that this structure can make sequentialization
compositional. Interfaces expose the values and control information that must
survive a computation, allowing alternative sharing and scheduling decisions
to be considered together with their storage costs. The objective is to retain
VSDG's optimization freedom while providing systematic operations for
constructing and comparing sequential implementations.

Implementations and their correctness evidence are constructed together in
Lean using dependent polynomial specifications. The current implementation
includes the diagram language, executable and relational semantics, verified
composition, and dependency ordering and pure-computation merging for a
straight-line fragment. The broader correspondence with VSDG control, sharing,
and loop transformations, together with target-specific lowering, remains
under development.

# Libraries

## Prelude

A general-purpose constructive Lean 4 prelude for work on polynomial
interfaces, along with various standard interfaces.

It features a Type-valued identity, decisions, indexed data, Type-valued
relations and loops, containers as polynomial interfaces, computations and
implementations on an interface, and specifications with verified
implementations. Its declarations depend on no axiom, and its evidence
computes. See the [API reference](docs/API.md).

| Library         | Role                                                                                                  | Axiom dependencies |
| --------------- | ----------------------------------------------------------------------------------------------------- | ------------------ |
| `Prelude`       | Type-valued identity, decisions, indexed data, relations, containers, and dependent evidence          | None               |
| `Prelude.Eq`    | Conversion of Lean's `Prop` equality into Type-valued identity. `import Prelude` does not include it. | None               |
| `Prelude.Axiom` | Optional function extensionality. `import Prelude` does not include it.                               | `Quot.sound`       |

## The Draft

`Draft` is a compiler IR on the Prelude. It has one diagram syntax over a
signature of pure and effectful operations, the function meaning of a diagram,
the verification of a diagram by its constructors, and an example frontend for
a typed fragment of Stele. `Frontend` translates the Stele syntax of
[EquiVM](https://github.com/argotorg/EquiVM) to that fragment, and it compares
the runs of the compiled functions with the interpreter of EquiVM.
[PLAN.md](PLAN.md) gives the stages and their status, [CONCEPT.md](CONCEPT.md)
gives the working design document.

## Build

Lean 4.29.0 is pinned in `lean-toolchain`.

```sh
lake build    # the Prelude, the Draft, the frontend, the probes, and their checks
```

## LLM Disclosure

The current materials use LLMs to formalize the current proof of concept under
the direction of the author. Once sufficient evidence has been produced it will
be prudent to pursue a hand-written formalization of the design, as an author
must be responsible for the correctness of the design and its formalization.
