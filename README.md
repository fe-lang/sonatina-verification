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

## Build

Lean 4.29.0 is pinned in `lean-toolchain`.

```sh
lake build    # the Prelude and its tests
```
