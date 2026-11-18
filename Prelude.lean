import Prelude.Identity
import Prelude.Decision
import Prelude.Indexed
import Prelude.Relation
import Prelude.Container

/-!
# Prelude

A constructive library for polynomial interfaces. It has an identity type in `Type`, decisions,
positions and environments over lists, relations and loops in `Type`, and containers with
their computations, implementations, specifications, and machines.

The Prelude uses Lean's `Nat`, `Fin`, `List`, `Vector`, `Option`, `Except`,
`Prod`, `Sum`, `Sigma`, `Empty`, `Unit`, and standard function and effect interfaces.
Its additional evidence types live in `Prelude`. Identity notation is enabled by
`open scoped Prelude`. `Prelude.Eq` and `Prelude.Axiom` are separate imports.
-/
