# AGENTS.md

## Constructivity is mandatory

**The compiler implementation is constructive: each of our declarations must not
depend on noncomputable axioms.**

1. **No axiom.** No declaration depends on an axiom or is `unsafe`, `partial`,
   `opaque`, or `noncomputable`. Thus `sorry`, `native_decide`, `funext`,
   `propext`, `Quot.sound`, and `Classical.choice` are not available.
   Prelude has no exemption.
2. **Computation.** A kernel check eliminates the actual witness and closes by
   `.refl`, with arbitrary values where possible. Freedom from axioms does not
   show that evidence computes: an identity that passes through `Prop` has no
   axiom and can fail to reduce.

This guidance applies to our declarations, and not to the tools that make them.
Tactics, the elaborator, and scripts use Lean's library, which depends on
axioms. The matchers that Lean generates for pattern matching on an indexed
family contain eliminators of `Eq` and `HEq`.

Two guidelines to follow:

- **Evidence stays in `Type`.** Evidence that a later construction consumes is
  data. Do not put it in `Prop`, in `Nonempty`, or in an existential
  proposition, and do not use proof irrelevance in place of a computation.
  `Prop` is for side conditions that no construction eliminates into data,
  such as bounds and decidable conditions.
- **No axiom as an assumption.** Extensionality or choice that enters as a
  parameter, a class instance, a quotient, or an opaque constant has the
  effect of the axiom. An interface premise needs a constructive instance,
  as we intend for all things in this library to compute.

For a more general and easy to follow heuristic: we work under the subset of
Lean that has a faithful translation to Idris2.

## Construction method

Foundational types, operations, and reusable laws belong in Prelude. Inspect and
reuse its existing APIs before introducing a definition. Extend or improve the
owning Prelude module when functionality is missing; do not duplicate it in
Draft, introduce parallel foundational types, or add wrappers that merely rename
the same functionality. Compiler-specific constructions, experiments, and checks
live outside the Prelude.

## Verification

A check that exceeds Lean's default limits has a cause in a construction. Find
the cause. Never disable kernel checking or raise a resource limit for
acceptance. `python3 scripts/profile_lean.py PATH.lean` gives the elaboration
time and the kernel time of one module.
