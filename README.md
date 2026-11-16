# Prelude

A general-purpose constructive Lean 4 prelude for work on polynomial
interfaces.

The Prelude has Type-valued identity, decisions, indexed data, Type-valued
relations and loops, containers as polynomial interfaces, computations and
implementations on an interface, and specifications with verified
implementations. Its declarations depend on no axiom, and its evidence
computes. See the [API reference](docs/API.md).

## Libraries

| Library | Role | Axiom dependencies |
| --- | --- | --- |
| `Prelude` | Type-valued identity, decisions, indexed data, relations, containers, and dependent evidence | None |
| `Prelude.Eq` | Conversion of Lean's `Prop` equality into Type-valued identity. `import Prelude` does not include it. | None |
| `Prelude.Axiom` | Optional function extensionality. `import Prelude` does not include it. | `Quot.sound` |

## The Draft

`Draft` is a compiler IR on the Prelude. It has one diagram syntax over a
signature of pure and effectful operations, the function meaning of a diagram,
the verification of a diagram by its constructors, and an example frontend for
a typed fragment of Stele. [PLAN.md](PLAN.md) gives the stages and their
status, [CONCEPT.md](CONCEPT.md) gives the design, and `Probes` has
explorations that are not parts of the implementation.

## Build

Lean 4.29.0 is pinned in `lean-toolchain`.

```sh
lake build    # the Prelude, the Draft, the probes, and their checks
```
