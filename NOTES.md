# Research observations and source contracts

Observations that constrain the translation of VSDG structure into polynomial
wiring, and the source contracts that the implementation must reproduce. Each
observation gives its argument, its consequence for the design, and the
[PLAN](PLAN.md) stage that must establish it with constructive evidence.
No observation has a proof in this repository until that stage is complete.

## Observations

### N1. Whole-component scheduling hides admissible schedules

Let `A` precede `B`, and let `C` be independent. The dependency-respecting orders
are `A B C`, `A C B`, and `C A B`. A generator that composes the diagrams
`(A; B)` and `C` as indivisible units produces `A B C` and `C A B` only. The
order `A C B` is a valid polynomial diagram with the same pure meaning for all
total primitive functions, and its call log differs from both block orders.

A generator can cover every choice of its own expression grammar and still omit
source-admissible orders. Completeness for a convenient grammar is a weaker
claim than coverage of the source's admissible implementations. The limitation
belongs to the generator: open traced polynomial wiring expresses the omitted
order. An open diagram with a boundary and component contracts is not an RVSDG
region, and it does not commit the source to a nested hierarchy.

**Consequence:** derive sequential realizations from source dependencies. Specify
admissibility independently of the generator. A chosen decomposition of a
diagram adds no ordering constraint.

**Established by:** D3. The three orders from one graph are a required check.

### N2. A retained value is not a retained control distinction

A polynomial routing map chooses its destination shape from its source shape.
The values in its data positions cannot change that choice. A value kept in a
bypass therefore does not let later routing recover which branch produced it.

In Figure 5.7, let each leaf execute only its two selected computations. One
untagged continuation after `A` cannot serve both paths `T` and `FF` while one
untagged continuation after `X` serves both `T` and `FT`. The obstruction
assumes no later test and no retained control shape. It does not rule out
richer realizations.

**Source:** Lawrence §2.4.3 says that a CFG node stores one continuation, and
that a node with `i` distinct continuations needs `i` copies. §5.1 gives the
alternatives for an operator that two paths use: one shared copy when the
continuation is common, static duplication, or additional dynamic tests. The
VDG form in §5.1 passes a return address. A bypass case in Kondyrev–Spivak is
such a stored return address.

**Consequence:** sharing must account for the control information needed after
reconvergence. A bypass `Σ j, y^(A j)` keeps the case `j` together with its
data, and a frame is the form of a diagram with that bypass. A path that does
not use the shared diagram exits past the frame. Additional control shapes,
tests, or duplicated continuations are explicit constructions with explicit
costs.

**Established by:** D2 for the saved-tag check; D4 for Figure 5.7.

### N3. Equal final stores can conceal an invalid transformation

Take `if P then f(g(h(x))) else f(g'(h(x)))`, where `h` reads the state and the
predicate `P` writes it. Moving `h` before the test changes the returned value.
Both orders can leave the same final store. When `h` is pure, the sharing
equation holds, and `P`, `g`, `g'`, and `f` can be effectful.

**Consequence:** a transformation law needs an operation-specific effect
condition and an observation contract that includes returned values. Agreement
of final state is insufficient. Equal source values do not imply equal
instrumented logs or equal costs.

**Established by:** D2 for pure centrality and the read/write equations; D4 for
reuse and tail sharing. The state-sensitive counterexample is a required
negative check.

### N4. Exact resolution of silent routing needs finite control, not finite data

When control shapes are finite, silent routing either reaches an exit, reaches a
missing route, or revisits a shape. A revisited shape proves that routing
continues without end, even when the backward maps permute data positions,
because position values cannot affect the next shape. The bound is the number
of control shapes. No fuel cutoff is necessary. Substitution can create silent
cycles that no component contains, so closure under substitution is a separate
obligation.

**Consequence:** finite control is a constructive composition domain with
unrestricted data, response, and runtime types. It does not decide termination
of effectful program loops. A partial routing map sends both a missing route
and silent divergence to `none`; a contract that separates failure from
divergence needs a finer observation.

**Established by:** D5.

### N5. Retained positions expose a storage obligation

When two regions are composed, the outer bypass can hold the first result
through the full execution of the second region. The bypass shows that the
value stays available. It does not assign physical storage. Placement
annotations that are correct for each region do not compose into a global
register allocation.

**Consequence:** local realization certificates and instruction counts do not
add up to a machine-level cost account. Lowering must account for retained
values, register conflicts, moves, and spills across region boundaries. The
thesis states these costs for a register machine. The EVM target has an
operand stack, so each cost account names its machine model.

**Established by:** D7.

### N6. Slow elaboration is not slow kernel checking

A boundary identity between large polynomial extensions can cost minutes when
one `Identity.refl` leaves all reductions to the elaborator. In one measured
case, an associativity module took 258 seconds to check. Elaboration took
almost all of that time, and kernel checking took 0.1 seconds. The same statement checked in 1.7 seconds after explicit normalization
of the boundary, followed by separate constructor, shape, and position
identities.

With the default `smartUnfolding`, the elaborator reduces the recursion
argument of a structurally recursive function again at each call, and it has
no cache for a term with free variables. The time of a nested run then grows
by a constant factor for each level. With `smartUnfolding false`, the
elaborator unfolds the recursion by its recursor, as the kernel does, and the
growth is linear. With that option, the elaborator also writes an implicit
argument that it computes in recursor form. The code generator rejects a
definition that has such an argument: "code generator does not support
recursor `List.rec` yet".

A `match` on an indexed family compiles to a matcher that eliminates `Prop`
equalities of the index and of the value, also when the index is a variable.
The elaborator then compares the values again at each step. A function that
uses `casesOn` with an explicit motive eliminates no equality. One check of
two interchanges unfolded `Eq.rec` 226,639 times and stopped at the default
limit with matchers on environments and positions. With `casesOn`, it passes.

A matcher on an identity proof has this cost at each use. The elaborator
reduces the proof, and then it compares the proof with `Identity.refl` by
unification, which reduces the proof again. With matchers in `Identity.cong₂`
and the other identity functions of the Prelude, the check `getGetPayload` of
[Draft/Checks/State.lean](Draft/Checks/State.lean) takes 6.7 s in the
elaborator and 0.35 s in the kernel. With `Identity.ind`, it takes 0.7 s in
the elaborator. With constants in place of its variables, the elaborator has
its cache, and the two times are 1.1 s and 0.3 s.

`Free.bind` goes through its first argument again at each level. A sequence
of `n` calls that binds its earlier part has `n²/2` crossings of a bind. Two
runs of Aberlé's fold on 512 elements take 21 s and 6.5 GiB in the kernel. The
same calls, each with the calls after it in its continuation, take 0.55 s.
`foldAgreement` in [Draft/Checks/Fold.lean](Draft/Checks/Fold.lean) relates
the two forms, and a lift moves along it.

**Consequence:** separate elaboration from kernel checking before a slowdown
is attributed to the mathematical design. Each kernel check in `Draft` sets
`smartUnfolding false`, and a definition of a diagram keeps the default.
Build a long sequence through its continuations, with
`bind` as the specification. Write a function on an indexed family that a
check evaluates many times with `casesOn` and an explicit motive. State boundary identities through explicit
eliminators whose motives expose the changing indices, and prove position
identities pointwise.

**Applies to:** all stages. D5 has the largest boundary identities.

### N7. Data incidence and operation order are different information

The operands of the steps of a diagram connect each operand and each output
to its producer. This incidence is the dependency graph of the diagram, and
it has no operation order. A diagram also has an order of its steps: each
step selects its operands from its context and keeps the context through its
operation. Different admissible orders have the same incidence and the same
pure result with different call logs.

**Consequence:** the translation relates a source diagram to a family of
[realizations](CONCEPT.md#source-object-and-admissible-realizations). The
order of the steps of one diagram is one choice from that family. It is not
the source dependency structure. Producer provenance, operation order, and
returned value are three separate proof obligations. Pure incidence does not
settle source control, state, or feedback.

**Established by:** D3.

### N8. Axiom-free evidence is not computational evidence

Function extensionality in Lean depends on `Quot.sound`. A Type-valued identity
built from it is accepted by dependent transport and does not reduce. Compiled
execution erases the witness, so an executable test passes while the kernel
cannot compute through the proof. Laws stated as identities of whole functions
or whole polynomial maps make every dependent consumer inherit this defect.

An identity built from a Lean `Prop` equality (`Identity.ofEq`) has no axiom
dependency. It reduces only when its endpoints are definitionally equal. A
dependency check accepts it.

**Consequence:** state laws through pointwise and structural relations whose
witnesses are built by recursion. Compose dependent preconditions and response
witnesses along the constructors of the computation. Acceptance evidence is a
kernel check that eliminates the actual witness and closes by `.refl`. The
axiom check and compiled tests are supplements.

**Applies to:** all stages.

## Source contracts

### Lawrence's source semantics

Sections 2.6.7 and 2.7 (pp. 43–47) distinguish value edges, dynamically linear
state use, observable results, and sets of admissible execution traces.
Sequentialization narrows the allowed traces and preserves observables. For the
finite pure fragment, §2.7.2 defines observations by the final result markings,
with non-strict gamma selection.

The trace set of §2.7.3 ranges over evaluation strategies and orders, and over
the nets that hash-consing, node cloning, and flattening produce. The number
of evaluations of a stateful node is fixed. Speculation is finite, so it adds
no non-termination (§2.7.2).

A gamma node selects between two tuples of operands, and a tuple can contain
the state (§2.6.2). Its reduction rules are `γ(true, v, ∘) ↦ v` and
`γ(false, ∘, v) ↦ v`, where `∘` needs no marking (§2.7.2). A state edge marks
each operation that has a side effect or that can fail to terminate, and each
other operation can be speculated (§2.2.3). Appendix B.2 translates a gamma
node on the state to a conditional in the state monad. Appendix B.4 forbids
the application of one stateful operation to two different states.

The absence of a state edge does not make an operation total. Appendix B.7
prefers an explicit gamma test before an operation that can raise an
exception, such as a test for a zero divisor. That operation has no state
edge, and the thesis names its speculation as an open issue.

Sections 5.2–5.3 (pp. 99–103) define sharing on an unshared VSDG as explicit
partitions. The presentation in §5.2 is stateless (footnote 3). Reuse and tail
partitions intersect only on identical nodes, and they commute. Shared
transitions require corresponding operand and result sharing. Reuse sharing
follows matching producers. Tail sharing follows matching consumers and
mutually exclusive alternatives. Shared places impose register-coalescing
constraints. Shared gamma nodes introduce the same-dependants rule and a
restriction on speculative writes.

One operation box at a join does not establish these obligations.

The thesis leaves two items informal. Footnote 18 of §2.7.3 leaves the
relation between reduction steps and program operations informal. §5.3 defines
the speculative-write restriction through the produced PDG and leaves an
internal form to future work.

### Fixed-occurrence pure dependencies

Source: §2.2.2 (pp. 28–29). The fragment has unique producers, ordered
operands, and topological orders that respect operand dependencies. It is
finite, acyclic, total, pure, and single-result, and every operation occurrence
executes once. Branches, loops, state edges, sharing partitions, duplication,
and speculation are outside it.

Required checks:

| Graph | Expected realizations |
| --- | --- |
| `A` precedes `B`; `C` independent | Exactly `A B C`, `A C B`, `C A B` |
| Diamond with a join that uses one operand twice | Both dependency-respecting consumer orders; the repeated operand keeps one producer |
| Output selection that discards a computed value | The discarded occurrence still executes once |

### Figure 5.6: reuse followed by tail sharing

Source: p. 100, with definitions on pp. 99–102.

```text
if P then f(g(h(x))) else f(g'(h(x)))
```

The depicted result computes `h(x)` once before the test of `P`, evaluates only
the selected `g` or `g'`, and computes one shared `f` after reconvergence. The
two `h` occurrences have reuse sharing. The two `f` occurrences have tail
sharing. The corresponding argument and result places share registers. The
unshared realization has seven boxes and the shared realization has five,
with the predicate test as an explicit box. A run executes four calls, the
test included.

### Figure 5.7: incompatible sharing opportunities and speculation

Source: §5.3.1, pp. 103–104.

```text
if P1 then (A, X) else if P2 then (B, X) else (A, Y)
```

The paths are `T`, `FT`, and `FF`. The result places of the first component
are coalesced as `r1`, and those of the second as `r2`. Neither register
occurs in the computations `A`, `B`, `X`, `Y`. Each of `A`, `B`, `X`, `Y` counts
as one abstract instruction. All arrangements execute one test on `T` and two
on `FT` and `FF`.

| Native arrangement | Static non-test instructions | Dynamic non-test instructions on `T / FT / FF` | Work outside the selected source leaf |
| --- | --- | --- | --- |
| 5.7(a), CFG sharing `X` | 5: two `A`, one each `B`, `X`, `Y` | 2 / 2 / 2 | None |
| 5.7(a), CFG sharing `A` | 5: two `X`, one each `A`, `B`, `Y` | 2 / 2 / 2 | None |
| 5.7(b), reuse sharing `A`, `X` | 4: one each `A`, `B`, `X`, `Y` | 2 / 3 / 3 | `A` on `FT`; `X` on `FF` |
| 5.7(c), mixture with two moves | 6: one each `A`, `B`, `X`, `Y`, two moves | 3 / 3 / 3 | `A` on `FT`; moves on `T`, `FF` |
| 5.7(c), mixture that shares the move | 6: `A`, `B`, `Y`, two `X`, one move | 3 / 3 / 3 | `A` on `FT`; moves on `T`, `FF` |

In (b), reuse sharing speculates `A` and `X` before the tests. In (c), `A` is
held in an additional register `rA`, and explicit moves copy it into the
coalesced result register. Both mixtures use `rA`.

For a total pure interpretation, the returned pair is `(A, X)`, `(B, X)`, or
`(A, Y)` on the three paths. Speculation of partial or effectful operations
needs its own semantic conditions. A claimed improvement on (a) must preserve
its baseline under the original assumptions and account for each additional
test, retained tag, storage location, and recomputation.

### Loops

Source: §2.6.6, §2.7.2, §2.7.3, §5.4 (pp. 105–106), and §5.5.2. A VSDG has
no cycle. A loop is an infinite graph, written with the `μ` operator
(§2.6.6). Its meaning is the limit of the meanings of the finite approximants
`Gⁿ`. `Gⁿ` is `G` after `n` flattenings of all its complex nodes, with `⊥` at
each place that is still the result of a complex node, and at each place
below a bound on the depth from the root (§2.7.2). The RVSDG is finite. Its `iter` node names a net that contains the
node, and it is a jump to the entrance of that net (§5.5.2).

A loop in the unshared VSDG is an infinite unfolding. Sharing partitions on
that unfolding give the loop choices:

| Choice | Sharing in the unfolding |
| --- | --- |
| Unpeeling | The operations of the first iteration have no tail sharing with the later iterations. `while (P) do C` becomes `if (P) {C; while (P) do C}`. |
| Unrolling | Each body operation is tail-shared with its equivalent at a fixed distance of more than one iteration (Figure 5.9(b)). |
| Software pipelining | Only some operations of the first iterations are tail-shared. Figure 5.9(a) speculates one copy of the repeated operation. |
| Placement of an invariant operation | Copies that are tail-shared across iterations execute in each iteration. Copies that are reuse-shared execute once (Figure 5.10). |

A level of pipelining, with its unpeeling and unrolling, is a pair of
isomorphic cuts across the unfolding. The VSDG specifies no level of
pipelining, because hash-consing is permitted across iterations (§2.7.3).

### Stele and EVM: failure, gas, and loops

Stele is the example frontend, and the EVM is the example backend. Source:
EquiVM at revision `fc74a64` and EVMLean at revision `fd4f5e6`. The paths
below are relative to each package.

| Fact | Location |
| --- | --- |
| Stele arithmetic uses unbounded integers. `add`, `sub`, and `mul` are total. `div`, `mod`, `sdiv`, and `srem` revert for a zero divisor. | EquiVM `Stele/Semantics/ValueOps.lean`, `evalBinaryOp?` |
| A Stele evaluation returns a value, reverts, or stops with an error for an ill-formed program. | EquiVM `Stele/Result.lean`, `EvalResult` |
| EVM `DIV` and `MOD` are total and return zero for a zero divisor. | EVMLean `Ethereum/UInt256.lean`, `div`, `mod` |
| The EVM exceptions are `OutOfFuel`, `InvalidInstruction`, `OutOfGass`, `BadJumpDestination`, `StackOverflow`, `StackUnderflow`, `InvalidMemoryAccess`, and `StaticModeViolation`. The stack limit is 1024 items. `DUP16` needs 16 items and `SWAP16` needs 17. | EVMLean `Ethereum/Exception.lean`, `Ethereum/Semantics.lean` (`Z`), `Ethereum/Instr.lean` |
| EVM execution has a fuel argument. Fuel above the available gas never gives `OutOfFuel`, so gas bounds each execution. | EVMLean `Ethereum/Semantics.lean` (`X`), `Ethereum/Theory/NoOutOfFuel.lean` |
| A Stele `while` has an inductive big-step relation. The executable interpreter has a fuel argument and an oracle, with soundness and completeness theorems against the relation. | EquiVM `Stele/Semantics/Exec.lean` (`ExecStmt`), `Stele/Interp/Sound.lean`, `Stele/Interp/Complete.lean` |
| Stele tracks no gas. `gasleft()` returns any word, and the gas of an external call is existential. | EquiVM `Stele/Semantics/Exec.lean` (`letGas`), `Stele/Semantics/Calls.lean` |
| Refinement relates a successful EVM run to a Stele result with equal final account maps and related return data. An EVM revert refines a Stele revert, and its payload has no constraint. | EquiVM `Stele/Refine.lean`, `execResultsEquiv` |
| When the EVM run has no gas left, refinement holds for each Stele result. The relation does not force termination. | EquiVM `Stele/Refine.lean`, `runtimeRefinementFor.outOfGas` |

Consequences:

- A Stele division is a test for a zero divisor, a revert in one case, and the
  total EVM division in the other case. The EVM division is a total pure
  operation, so it can be before the test. The revert cannot.
- The refinement relation of EquiVM does not preserve gas. For that
  observation, each total pure EVM operation satisfies copy and discard
  naturality, and gas is a cost.
- The direction from source runs to target runs needs a statement that the
  refinement relation does not give: a gas bound above which the run of the
  generated code does not end with out-of-gas.
- The refinement relation does not compare the state after a revert, so an
  effect before a revert has no observation at this boundary. The equation
  sets keep the order of effects.
- The source and the target define loops with an inductive relation and a
  function with fuel. The target has no divergence, because gas bounds each
  execution.
- A stack underflow, a stack overflow, and a bad jump destination are
  obligations of the lowering. The source has no equivalent failure.

### The four products

Polynomial coproduct combines control alternatives. The tensor of the port
category places values next to one another, and whiskering by it keeps bypass
context. With discrete type labels, that action is the polynomial product.
Polynomial substitution composes functors. No two of these are identified
implicitly. The `+` notation that `Int` inherits does not make `Int(Poly_*)`
cocartesian.

### Source files

The repository does not contain these files. Each row gives the public
location of a source, the file that the labels and page numbers of these
documents refer to, and the SHA-256 of that file.

| Source | File | SHA-256 |
| --- | --- | --- |
| [Lawrence, Optimizing compilation with the Value State Dependence Graph, University of Cambridge Computer Laboratory Technical Report UCAM-CL-TR-705, 2007](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-705.pdf) | The PDF | `94342fb7e365ef9fcb46093026bbf175a5c5d72dafe9fc32474c9272239f86a6` |
| [Kondyrev–Spivak, The compact double category Int(Poly\*) models control flow and data transformations, 2025, arXiv:2509.05462](https://arxiv.org/abs/2509.05462) | `int-poly-control.tex` in the TeX source | `291c7032c7712680713b8b17c48059fc3f825348834216eaff3f6a0b22ae1588` |
| [Román–Sobociński, String diagrams for premonoidal categories, 2023, arXiv:2305.06075](https://arxiv.org/abs/2305.06075) | `arxivmain.tex` in the TeX source | `22ab11b9727b5bd4acef1dc282957441308679a054d94cdd0d741eb84ae4a855` |
| [Aberlé, Compositional program verification with polynomial functors in dependent type theory, 2026, arXiv:2604.01303](https://arxiv.org/abs/2604.01303) | `paper-eptcs.tex` in the TeX source | `297915e3565d0e9c782ac2552d4963dbc0b9bb88ede4752f73e518611f4aefc2` |

### Reference files

The design takes no construction from these files. [CONCEPT.md](CONCEPT.md)
names them where a published form is near an obligation of the design. The
repository does not contain them. Each hash is the SHA-256 of the PDF that
the page numbers of these documents refer to.

| Reference | SHA-256 |
| --- | --- |
| [Jeffrey, Premonoidal categories and a graphical view of programs, 1997](https://asaj.org/papers/premonA.pdf). This copy has no appendix. | `c7ee5e5c8ec0955dbd9966f71c6410fd6a69bf2c4b54987a0c6867280cefe989` |
| [Benton–Hyland, Traced premonoidal categories, 2003](https://www.numdam.org/item/ITA_2003__37_4_273_0.pdf) | `667e8831335536d7c1bee779ff47a9395467687fb64e48734e2cb5104e9bf81f` |
| [Hasegawa, The uniformity principle on traced monoidal categories, 2004](https://www.kurims.kyoto-u.ac.jp/~hassei/papers/prims04.pdf) | `8bd9f31179baecd85e2d99c45ec839ac2ea23707b6ee62d8a7ab41ed6c4221d0` |
| [Staton, Freyd categories are enriched Lawvere theories, 2014](https://www.cs.ox.ac.uk/people/samuel.staton/papers/freyd-lawvere-2014.pdf), author's preprint | `695c134459b17486232f6c0eb6728a2757088a581386a8615c6a283a3fae47e2` |
| [Goncharov–Milius–Rauch, Complete Elgot monads and coalgebraic resumptions, 2016, arXiv:1603.02148](https://arxiv.org/abs/1603.02148) | `12e91f09ff94c59f13a3fb1ca3fcbd30ff0a93e22213c1356348dfe6f3ff2468` |
| [Goncharov–Schröder–Rauch–Piróg, Guarded and unguarded iteration for generalized processes, 2019, arXiv:1712.09574](https://arxiv.org/abs/1712.09574) | `3db24b769a6ccabe33c8c470847e756d20b3d715048addffd60bf7a6aa27a0ae` |
| [Bonchi–Di Giorgio–Santamaria, Deconstructing the calculus of relations with tape diagrams, 2022, arXiv:2210.09950](https://arxiv.org/abs/2210.09950) | `527caeb8235037f87b9e85809680f891e6e94df656e8fbf1bed3541ef147810c` |
| [Bonchi–Di Giorgio–Di Lavore, A diagrammatic algebra for program logics, 2024, arXiv:2410.03561](https://arxiv.org/abs/2410.03561) | `c33d257b9db7fbe5c3642d224e372768898be389c5e1a31aa14010a08da85e84` |
| [Ghalayini–Krishnaswami, The denotational semantics of SSA, 2024, arXiv:2411.09347 version 2](https://arxiv.org/abs/2411.09347v2) | `d04c46f9b4e5084414c003acfdb86f7c2506787e026d9df1685722c603c5143e` |
| [Bonchi–Cioffo–Di Giorgio–Di Lavore, Tape diagrams for monoidal monads, 2025, arXiv:2503.22819](https://arxiv.org/abs/2503.22819) | `76f1f158afc51fd8135c72da463f5dac3b5dbc6cf8392878bfcc178a890df9a0` |
| [Bonchi–Di Giorgio–Di Lavore, A diagrammatic basis for computer programming, 2025, arXiv:2512.07240](https://arxiv.org/abs/2512.07240) | `e9adf578697d87b09fc0b7339b0e0fd6f95fe304d7efbb197383d20aa868f319` |
