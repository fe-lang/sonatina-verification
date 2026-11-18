import Draft.Sequentialization
import Draft.Checks.Lift

/-! The orders of the steps of three source diagrams.

The first group has three steps. `A` and `B` are pure, and `B` uses the output of `A`. `C` is
effectful and uses the first input only. The source diagram has the order `A B C`.

`C` is ready in the source diagram: it moves past `B` and then past `A`. The orders `A C B` and
`C A B` are two diagrams, and each has the evidence that it is an order of the source diagram.
The source diagram is an order of itself. Each order gives the same two values, for arbitrary
inputs and an arbitrary response of the store. The derivation of each order is in the
interchange equation set, and a check consumes its soundness through a dependent payload that
has the response of the store.

The source diagram is a diagram of the fragment with fixed occurrences. Its ready steps are `A`
and `C`: `B` has the output of `A` as an operand. The list of its orders has the three orders
and no other order, and each order of the list gives the same two values. The list is
complete: the theorem gives an order of the list for each order. For the evidence of the three
orders above, which is not from the list, it gives the three positions of the list. A check
consumes the agreement of the order `C A B` with the order of the list through a dependent
payload that has the response of the store.

The source diagram has a verified implementation: its lift for a specification with an
admission, and then the verified lowering. The map of verified implementations along the
derivation of an order gives the verified implementation of the order. The receipt at the exit
of the source diagram, of the order `A C B`, and of the order `C A B` gives the same payload
through its identity, for an arbitrary admission. A check consumes the postcondition of `B` in
the evidence of the order `C A B` through a dependent payload.

The dependency graph of the source diagram has the occurrences of its three steps at the
histories of its inputs. The orders `A C B` and `C A B` have the same occurrences in the other
order: no occurrence changes. A check consumes the identity of the theorem of the move of `C`
through a dependent payload. The word of each order has the number of each ready step. The
evidence that the word of the order `C A B` is an admissible order comes from the theorem. It
runs on the machine of the runs, and a check consumes the identity that no occurrence remains.
The done occurrences at the end are the occurrences of the order, with the last run first. A
word that starts with `B` has no evidence, because the call of an operand of `B` is not done.
The derivation from the source diagram to the order `C A B` keeps the occurrences: the
occurrence of `C` has the third position in the graph of the source diagram and the first
position in the graph of the order, the derivation in the other direction gives the position in
the source diagram, and a check consumes the round trip of a position through a dependent
payload.
No two of the three occurrences are equal, so an admissible order of the graph is the word of
an order. From the evidence of the word of the order `C A B`, the theorem gives an order with
the steps `C A B`, and a check consumes the identity of its word through a dependent payload.

The second group has a shared operand and a repeated operand. `A` is pure. `B` is pure and has
the output of `A` as its two operands. `C` is effectful and has the output of `A` as its
operand. `D` has the outputs of `B` and `C`. The list of the orders has the two orders of `B`
and `C`. Each order has four steps, so `A` has one occurrence, and each gives the same values.

The third group has a discarded value. `A` is effectful, and no step and no exit port has its
response. `B` is pure. The list of the orders has the two orders. After the lowering, each
order is one call of the store.

The fourth group has two equal calls. `A` is pure and has two calls at the two inputs, and `D`
has the outputs of the two calls. The copy rule relates this diagram to the diagram with one
call of `A`, in which `D` has the output of that call two times. The two diagrams give the same
values, and a check consumes the soundness of the rule through a dependent payload. The same
rule holds for a rest with two steps: `D`, and then the effectful `C` with the output of `D`.
A check consumes its soundness through a dependent payload that has the response of the store.
In the dependency graph, the two calls are one occurrence two times, and the two operands of `D` have
one history. The list of the orders has the two orders of the two calls. The word that runs one
call of `A`, then `D`, and then the other call of `A` is an admissible order of the occurrences,
and it is not the word of an order: `D` runs when one of the two calls is done. The evidence
runs on the machine of the runs, and a check consumes the identity that no occurrence
remains. The merged diagram of the diagram with two calls has one call of `A`. It gives the
same values, and a check consumes the soundness of its derivation through a dependent payload.
Its graph has the occurrence of `A` one time, and the merge gives the evidence that no two of
its occurrences are equal. With that evidence, the theorem of the other direction gives an
order of the merged diagram from the evidence of the word of its two runs. The link gives each
occurrence of the diagram with two calls its position in the graph of the merged diagram: the
two calls of `A` have one position. The occurrence of `A` in the graph of the merged diagram
has the position of the first call in the graph of the diagram.
A last diagram has the effectful `C` between the two calls of `A`. Its merged diagram has one
call of `A`: the derivation moves the second call before `C` by one interchange, and then it
uses the copy rule. A check consumes its soundness through a dependent payload that has the
response of the store. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Dependency

open Container
open Draft.Checks.Free (store provider)
open Draft.Checks.Dependent (Admission Receipt expected)
open Draft.Checks.Diagram (Op sig Value lower returns inputs values observe opSpec lowerDep)

abbrev Two : Exits Unit := [.one [(), ()]]

/-- The exit after the three steps: the output of `B` and the response of `C`. -/
def last : Diagram sig [(), (), (), (), ()] Two :=
  .exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩

/-- `C` is effectful, and its operand is the first input. -/
def stepC : Diagram sig [(), (), (), ()] Two :=
  .step ⟨.emit, .cons (.there (.there .here)) .nil⟩ fun | ⟨_, .here⟩ => last

/-- `B` is pure, and its operands are the output of `A` and the second input. -/
def stepB : Diagram sig [(), (), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there (.there .here)) .nil)⟩ fun | ⟨_, .here⟩ => stepC

/-- The source diagram: `A` on the two inputs, and then `B`, and then `C`. -/
def source : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun | ⟨_, .here⟩ => stepB

/-- The one case of an output boundary with one port. -/
def center : (Boundary.one [()] : Boundary Unit).Case := ⟨_, .here⟩

/-- The type of the cases of that boundary is contractible: each case is the one case. -/
def oneCase : IsContr (Boundary.one [()] : Boundary Unit).Case :=
  ⟨center, fun | ⟨_, .here⟩ => .refl⟩

/-- `C` is ready after `A`: it moves past `B`. -/
def pastB := Diagram.Ready.pastOne (S := sig) (b := Op.emit) (Qs := Two) Op.add (.inl .refl)
  (.cons .here (.cons (.there (.there .here)) .nil)) (.cons (.there .here) .nil)
  (rest := fun | ⟨_, .here⟩ => stepC) oneCase (.here _ _)

/-- `C` is ready in the source diagram: it moves past `B` and then past `A`. -/
def pastA := Diagram.Ready.pastOne (S := sig) (b := Op.emit) (Qs := Two) Op.add (.inl .refl)
  (.cons .here (.cons (.there .here) .nil)) (.cons .here .nil)
  (rest := fun | ⟨_, .here⟩ => stepB) oneCase pastB.2

/-- The source diagram is an order of itself: each step is the first step. -/
def sourceOrder : Diagram.Order source source :=
  ⟨_, .here _ _, fun
    | ⟨_, .here⟩ => ⟨_, .here _ _, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The order `A C B`. `C` has the first input, and `B` has the output of `A` and the second
input. The exit has the output of `B` and the response of `C`. -/
def middle : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun
    | ⟨_, .here⟩ => .step ⟨.emit, .cons (.there .here) .nil⟩ fun
      | ⟨_, .here⟩ =>
          .step ⟨.add, .cons (.there .here) (.cons (.there (.there (.there .here))) .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩

/-- The evidence of the order `A C B`: after `A`, the step `C` is ready past `B`. -/
def middleOrder : Diagram.Order middle source :=
  ⟨_, .here _ _, fun
    | ⟨_, .here⟩ => ⟨_, pastB.2, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The order `C A B`. -/
def front : Diagram sig [(), ()] Two :=
  .step ⟨.emit, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩ fun
      | ⟨_, .here⟩ =>
          .step ⟨.add, .cons .here (.cons (.there (.there (.there .here))) .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _,
                .cons .here (.cons (.there (.there .here)) .nil)⟩

/-- The evidence of the order `C A B`: the step `C` is ready past `B` and `A`. -/
def frontOrder : Diagram.Order front source :=
  ⟨_, pastA.2, fun
    | ⟨_, .here⟩ => ⟨_, .here _ _, fun
      | ⟨_, .here⟩ => ⟨_, .here _ _, fun
        | ⟨_, .here⟩ => .refl⟩⟩⟩

/-- The source diagram is a diagram of the fragment: each of its three steps has one output
case. -/
def straight : source.Straight := ⟨oneCase, oneCase, oneCase, ()⟩

set_option smartUnfolding false in
/-- Each order is a diagram of the fragment, and it has its steps in its order. -/
def orders :
    (Diagram.ops source straight,
      Diagram.ops middle (Diagram.Order.straight middle source middleOrder straight),
      Diagram.ops front (Diagram.Order.straight front source frontOrder straight)) ≡
      ([Op.add, Op.add, Op.emit], [Op.add, Op.emit, Op.add], [Op.emit, Op.add, Op.add]) :=
  .refl

variable (stop : Free (sig.interface Value) (Exits.At Two Value)) (count : Nat)

set_option smartUnfolding false in
/-- Each order gives the same two values, for arbitrary inputs and an arbitrary response of the
store. -/
def sourceRun (flag : Bool) (u v x y : Nat) :
    observe stop count source flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def middleRun (flag : Bool) (u v x y : Nat) :
    observe stop count middle flag u v x y ≡ (x + y + y, u + x) := .refl

set_option smartUnfolding false in
def frontRun (flag : Bool) (u v x y : Nat) :
    observe stop count front flag u v x y ≡ (x + y + y, u + x) := .refl

/-- The soundness of the derivation of an order: the source diagram and the order agree after
the lowering. -/
def sound (e : Diagram sig [(), ()] Two) (o : Diagram.Order e source) (x y : Nat) :
    Free.Agreement ((source.meaning stop count (inputs x y)).subst lower)
      ((e.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.Order.derivation (Rules.Map.id _) e source o).sound stop count
    (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the source diagram and of the order `A C B` is
consumed through a dependent payload that has the response of the store. -/
def middleSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count middle middleOrder x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The same for the order `C A B`, whose derivation has two interchanges. -/
def frontSound (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((sound stop count front frontOrder x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The ready steps of the source diagram are `A` and `C`. -/
def readySteps : (Diagram.choices source straight).map (fun choice => choice.1) ≡
    [Op.add, Op.emit] := .refl

set_option smartUnfolding false in
/-- The list of the orders of the source diagram has the three orders. -/
def allOrders :
    ((Diagram.orders source straight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 source r.2 straight)) ≡
      [[Op.add, Op.add, Op.emit], [Op.add, Op.emit, Op.add], [Op.emit, Op.add, Op.add]] :=
  .refl

set_option smartUnfolding false in
/-- Each order of the list gives the same two values, for arbitrary inputs and an arbitrary
response of the store. -/
def allRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.orders source straight).map fun r =>
        observe stop count r.1 flag u v x y) ≡
      [(x + y + y, u + x), (x + y + y, u + x), (x + y + y, u + x)] := .refl

set_option smartUnfolding false in
/-- The evidence of the three orders, which is not from the list, has the three positions of
the list of the orders. -/
def listedPositions :
    ((Diagram.Order.listed source source sourceOrder straight).2.1.toFin.val,
      (Diagram.Order.listed middle source middleOrder straight).2.1.toFin.val,
      (Diagram.Order.listed front source frontOrder straight).2.1.toFin.val) ≡ (0, 1, 2) := .refl

/-- The order `C A B` and the order of the list that the theorem gives agree after the
lowering. -/
def listedSound (x y : Nat) :
    Free.Agreement ((front.meaning stop count (inputs x y)).subst lower)
      (((Diagram.Order.listed front source frontOrder straight).1.1.meaning stop count
        (inputs x y)).subst lower) :=
  (Diagram.Derivation.agree (R := Rules.interchange sig)
      (Diagram.Order.listed front source frontOrder straight).2.2).sound stop count
    (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The agreement of the theorem is consumed through a dependent payload that has the response
of the store. -/
def listedPayload (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((listedSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-! The evidence of each order. -/

/-- The specification of the source diagram. The witness of its precondition is an admission.
The exit has the output of `B` as a function of the two inputs, and the response of `C` with a
receipt for the admission. -/
def sourceSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] Two) where
  Pre _ := Admission
  Post env pre out :=
    ((values out).1 ≡ env.lookup .here + env.lookup (.there .here) + env.lookup (.there .here)) ×
      ((m : Nat) × (((values out).2 ≡ m + env.lookup .here) × Receipt (expected pre m)))

/-- The lift of the source diagram, by the constructors of the diagram. The exit has the
postconditions of `A` and `B`, and the receipt of `C`. -/
def sourceLift (n : Nat) (env : All Value [(), ()]) (pre : sourceSpec.Pre env) :
    source.HoldsStill opSpec Empty n (sourceSpec.Post env pre) env :=
  Diagram.HoldsStill.step (S := sig) ⟨Op.add, .cons .here (.cons (.there .here) .nil)⟩ _ () fun
    | ⟨⟨_, .here⟩, .cons _ .nil⟩, sumA =>
        Diagram.HoldsStill.step (S := sig)
          ⟨Op.add, .cons .here (.cons (.there (.there .here)) .nil)⟩ _ () fun
          | ⟨⟨_, .here⟩, .cons _ .nil⟩, sumB =>
              Diagram.HoldsStill.step (S := sig) ⟨Op.emit, .cons (.there (.there .here)) .nil⟩ _
                pre fun
                | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt =>
                    Diagram.HoldsStill.exit _
                      ⟨sumB.trans
                          (Identity.cong (fun k => k + env.lookup (.there .here)) sumA),
                        receipt⟩

/-- The verified source diagram and then the verified lowering. -/
def loweredSource : ImplDep sourceSpec Verified.spec ((source.impl stop count).trans lower) :=
  (Diagram.HoldsStill.impl (sourceLift count) fun _ _ e => e.elim).trans lowerDep

/-- The verified implementation of an order: the map of verified implementations along the
derivation of the order. -/
def lowered (e : Diagram sig [(), ()] Two) (o : Diagram.Order e source) :
    ImplDep sourceSpec Verified.spec ((e.impl stop count).trans lower) :=
  (Diagram.Order.derivation (Rules.Map.id _) e source o).lift (.interchange returns) stop count
    (loweredSource stop count)

/-- The receipt at the exit, from a run with a provider that has evidence. -/
def receipt {f : Impl (Diagram.interface Value [(), ()] Two) store}
    (ff : ImplDep sourceSpec Verified.spec f) (flag : Bool) (u v x y : Nat) (pre : Admission) :
    Nat :=
  ((ff.run (Verified.verify flag u v)) (inputs x y) pre).2.2.2.read

set_option smartUnfolding false in
/-- The receipt of the source diagram has the response of the store, for an arbitrary
admission, arbitrary inputs, and arbitrary responses. The payload is a function of the
constructor of the admission. -/
def sourceReceipt (flag : Bool) (u v x y : Nat) (pre : Admission) :
    receipt (loweredSource stop count) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The evidence of the order `A C B` gives the same payload. -/
def middleReceipt (flag : Bool) (u v x y : Nat) (pre : Admission) :
    receipt (lowered stop count middle middleOrder) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The evidence of the order `C A B`, whose derivation has two interchanges, gives the same
payload. -/
def frontReceipt (flag : Bool) (u v x y : Nat) (pre : Admission) :
    receipt (lowered stop count front frontOrder) flag u v x y pre ≡ expected pre u := .refl

set_option smartUnfolding false in
/-- The postcondition of `B` in the evidence of the order `C A B` is consumed through a
dependent payload. -/
def frontSum (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (((lowered stop count front frontOrder).run (Verified.verify flag u v))
        (inputs x y) pre).1
      ⟨x + y + y, Nat.lt_succ_self _⟩).val ≡ x + y + y := .refl

/-! The dependency graph. -/

/-- The dependency graph of the source diagram: the occurrences of its steps at the histories
of its inputs. -/
def graph : List (sig.Occurrence [(), ()]) := source.graph straight

/-- The list with the element at a number at the front. -/
def toFront {α : Type} (k : Nat) (xs : List α) : List α :=
  match takeAt k xs with
  | none => xs
  | some found => found.1 :: found.2

set_option smartUnfolding false in
/-- The order `C A B` has the occurrences of the source diagram, with `C` at the front. No
occurrence changes. -/
def frontGraph :
    front.graph (Diagram.Order.straight front source frontOrder straight) ≡ toFront 2 graph :=
  .refl

set_option smartUnfolding false in
/-- The order `A C B` has them with `C` at the second position. -/
def middleGraph :
    middle.graph (Diagram.Order.straight middle source middleOrder straight) ≡
      toFront 1 (toFront 2 graph) := .refl

/-- The number of the other occurrences of a result of a move. -/
def others {α : Type} : Option (α × List α) → Nat
  | none => 0
  | some found => found.2.length

set_option smartUnfolding false in
/-- The identity of the theorem for the move of `C` past `B` and `A` is consumed through a
dependent payload. -/
def movedPayload :
    (Identity.transport (fun r => Fin (others r + 1))
      (pastA.2.moved (Γ₀ := [(), ()]) straight (sig.inputs _) none)
      ⟨2, Nat.lt_succ_self _⟩).val ≡ 2 := .refl

set_option smartUnfolding false in
/-- The word of each order: the number of each ready step. -/
def words :
    (Diagram.Order.depths source source sourceOrder straight,
      Diagram.Order.depths middle source middleOrder straight,
      Diagram.Order.depths front source frontOrder straight) ≡
      ([0, 0, 0], [0, 1, 0], [2, 0, 0]) := .refl

/-- The next runtime of a run: the remaining occurrences without the occurrence of the run, and
the done occurrences with it. -/
def progress : Option (sig.Occurrence [(), ()] × List (sig.Occurrence [(), ()])) →
    sig.Progress [(), ()] → sig.Progress [(), ()]
  | none, state => state
  | some found, state => (found.2, found.1 :: state.2)

/-- The machine of the runs. -/
def machine : Machine runs (sig.Progress [(), ()]) Empty :=
  fun a => .inr ((), progress (takeAt a.1 a.2.1) a.2)

/-- The machine has evidence of the specification of the runs. -/
def machineEvidence : Evidence (sig.admissible [(), ()]) machine :=
  fun a pre => Identity.cong (fun r => progress r a.2) pre.2.1

/-- The evidence that the word of the order `C A B` is an admissible order of the graph, from
the theorem. -/
def frontAdmissible :=
  Diagram.Order.admissible front source frontOrder straight (sig.inputs [(), ()]) none []
    Signature.Known.inputs ()

/-- The result of the run of a word on the machine, from the graph. -/
def ran (w : List Nat) : Empty ⊕ (Unit × sig.Progress [(), ()]) := machine.run (word w) (graph, [])

/-- The remaining occurrences at a result. -/
def remainingAt : Empty ⊕ (Unit × sig.Progress [(), ()]) → List (sig.Occurrence [(), ()])
  | .inr out => out.2.1

/-- The condition at the end of a word is the identity that no occurrence remains. -/
def finished : (r : Empty ⊕ (Unit × sig.Progress [(), ()])) → sig.Finished [(), ()] r →
    remainingAt r ≡ []
  | .inr _, h => h

set_option smartUnfolding false in
/-- The run of that evidence on the machine gives the identity that no occurrence remains. The
identity is consumed through a dependent payload. -/
def frontFinished :
    (Identity.transport (fun (l : List (sig.Occurrence [(), ()])) => Fin (l.length + 1))
      (finished (ran (Diagram.Order.depths front source frontOrder straight))
        (FreeDep.run machineEvidence frontAdmissible))
      ⟨0, Nat.zero_lt_succ _⟩).val ≡ 0 := .refl

/-- The done occurrences at a result. -/
def doneAt : Empty ⊕ (Unit × sig.Progress [(), ()]) → List (sig.Occurrence [(), ()])
  | .inr out => out.2.2

set_option smartUnfolding false in
/-- The done occurrences at the end of the word of the order `C A B` are the occurrences of the
order, with the last run first. -/
def frontDone :
    doneAt (ran (Diagram.Order.depths front source frontOrder straight)) ≡
      (front.graph (Diagram.Order.straight front source frontOrder straight)).reverse := .refl

/-- A result of a move has no occurrence with evidence that the call of each operand is done
for the empty list of done occurrences. -/
def Blocked : Option (sig.Occurrence [(), ()] × List (sig.Occurrence [(), ()])) → Type
  | none => Unit
  | some found =>
      ((t : Unit) → (p : Port (sig.input found.1.1) t) →
        History.Produced [] (found.1.2.args.lookup p)) → Empty

set_option smartUnfolding false in
/-- The second occurrence of the graph is blocked at the start: the call of the first operand
of `B` is not done. -/
def blocked : Blocked (takeAt 1 graph) := fun operands => nomatch operands () .here

/-- A word that starts with `B` has no evidence that it is an admissible order. -/
def notAdmissible (rest : List Nat)
    (h : FreeDep (sig.admissible [(), ()]) (sig.Finished [(), ()])
      ((word (1 :: rest)).thread (E := Empty) (graph, []))) : Empty :=
  Identity.transport Blocked h.parts.1.2.1 blocked h.parts.1.2.2.1

/-- The call of the first `A` of the first source diagram, at the histories of the inputs. -/
def firstA : Call sig [(), ()] Op.add :=
  .mk (.cons (.input .here) (.cons (.input (.there .here)) .nil)) none

/-- The call of `B`: the output of `A` and the second input. -/
def firstB : Call sig [(), ()] Op.add :=
  .mk (.cons (.output firstA center .here) (.cons (.input (.there .here)) .nil)) none

/-- The call of `C`: the first input. -/
def firstC : Call sig [(), ()] Op.emit := .mk (.cons (.input .here) .nil) none

/-- The occurrences of the first source diagram. -/
def sourceOccurrences : List (sig.Occurrence [(), ()]) :=
  [⟨Op.add, firstA⟩, ⟨Op.add, firstB⟩, ⟨Op.emit, firstC⟩]

set_option smartUnfolding false in
/-- The graph of the first source diagram has these occurrences. -/
def sourceGraph : graph ≡ sourceOccurrences := .refl

/-- No two of the three occurrences are equal. -/
def sourceDistinct : Elem.Distinct sourceOccurrences :=
  fun x i j =>
    match x, i, j with
    | _, .here, .here => .refl
    | _, .there .here, .there .here => .refl
    | _, .there (.there .here), .there (.there .here) => .refl

/-- The derivation from the source diagram to the order `C A B`. -/
def frontDerivation : Diagram.Derivation (Rules.interchange sig) source front :=
  Diagram.Order.derivation (Rules.Map.id _) front source frontOrder

/-- The order `C A B` is a diagram of the fragment. -/
def frontStraight : front.Straight := Diagram.Order.straight front source frontOrder straight

set_option smartUnfolding false in
/-- The occurrence of `C` has the third position in the graph of the source diagram and the
first position in the graph of the order. -/
def keptC :
    (((frontDerivation.graphKept straight frontStraight) ⟨Op.emit, firstC⟩).to
      (.there (.there .here))).toFin.val ≡ 0 := .refl

set_option smartUnfolding false in
/-- The derivation in the other direction gives the position in the source diagram. -/
def keptBack :
    ((((Diagram.Derivation.symm frontDerivation).graphKept frontStraight straight)
      ⟨Op.emit, firstC⟩).to .here).toFin.val ≡ 2 := .refl

set_option smartUnfolding false in
/-- The round trip of a position is the identity, and it is consumed through a dependent
payload. -/
def keptRound :
    (Identity.transport
      (fun (i : Elem (⟨Op.emit, firstC⟩ : sig.Occurrence [(), ()]) (source.graph straight)) =>
        Fin (i.toFin.val + 1))
      (((frontDerivation.graphKept straight frontStraight) ⟨Op.emit, firstC⟩).invTo
        (.there (.there .here))).symm
      ⟨2, Nat.lt_succ_self _⟩).val ≡ 2 := .refl

/-- The theorem gives an order of the first source diagram from the evidence that the word of
the order `C A B` is an admissible order of the graph. -/
def frontAgain :=
  Diagram.Order.ofGraph source straight
    (Identity.transport Elem.Distinct sourceGraph.symm sourceDistinct)
    (Diagram.Order.depths front source frontOrder straight) frontAdmissible

set_option smartUnfolding false in
/-- That order has the steps of the order `C A B`. -/
def frontAgainOps :
    Diagram.ops frontAgain.1 (Diagram.Order.straight frontAgain.1 source frontAgain.2.1 straight) ≡
      [Op.emit, Op.add, Op.add] := .refl

set_option smartUnfolding false in
/-- The identity of the word of that order is consumed through a dependent payload. -/
def frontAgainWord :
    (Identity.transport (fun (w : List Nat) => Fin (w.length + 1)) frontAgain.2.2
      ⟨3, Nat.lt_succ_self _⟩).val ≡ 3 := .refl

/-! A shared operand and a repeated operand. -/

/-- `A` on the two inputs. `B` has the output of `A` as its two operands. `C` is effectful and
has the output of `A` as its operand. `D` has the outputs of `B` and `C`. The exit has the
output of `D` and the output of `A`. -/
def diamond : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons .here (.cons .here .nil)⟩ fun
      | ⟨_, .here⟩ => .step ⟨.emit, .cons (.there .here) .nil⟩ fun
        | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons .here .nil)⟩ fun
          | ⟨_, .here⟩ =>
              .exit ⟨_, .here, Boundary.only _,
                .cons .here (.cons (.there (.there (.there .here))) .nil)⟩

/-- The diagram is a diagram of the fragment. -/
def diamondStraight : diamond.Straight :=
  ⟨oneCase, oneCase, oneCase, oneCase, ()⟩

set_option smartUnfolding false in
/-- The list of the orders has the two orders of `B` and `C`. Each order has four steps: `A`
has one occurrence. -/
def diamondOrders :
    ((Diagram.orders diamond diamondStraight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 diamond r.2 diamondStraight)) ≡
      [[Op.add, Op.add, Op.emit, Op.add], [Op.add, Op.emit, Op.add, Op.add]] := .refl

set_option smartUnfolding false in
/-- Each order gives the same two values. The output of `B` has the output of `A` two times,
and the response of `C` has it one time. -/
def diamondRuns (flag : Bool) (u v x y : Nat) :
    ((Diagram.orders diamond diamondStraight).map fun r =>
        observe stop count r.1 flag u v x y) ≡
      [(x + y + (x + y) + (u + (x + y)), x + y), (x + y + (x + y) + (u + (x + y)), x + y)] :=
  .refl

/-! A discarded value. -/

/-- `A` is effectful, and no step and no exit port has its response. `B` is pure, and the exit
has its output two times. -/
def discarded : Diagram sig [(), ()] Two :=
  .step ⟨.emit, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩ fun
      | ⟨_, .here⟩ => .exit ⟨_, .here, Boundary.only _, .cons .here (.cons .here .nil)⟩

/-- The diagram is a diagram of the fragment. -/
def discardedStraight : discarded.Straight := ⟨oneCase, oneCase, ()⟩

set_option smartUnfolding false in
/-- The list of the orders has the two orders. -/
def discardedOrders :
    ((Diagram.orders discarded discardedStraight).map fun r =>
        Diagram.ops r.1 (Diagram.Order.straight r.1 discarded r.2 discardedStraight)) ≡
      [[Op.emit, Op.add], [Op.add, Op.emit]] := .refl

set_option smartUnfolding false in
/-- After the lowering, each order is one call of the store: the step with the discarded
response has one execution in each order. -/
def discardedCalls (x y : Nat) :
    ((Diagram.orders discarded discardedStraight).map fun r =>
        (r.1.meaning (X := Value) stop count (inputs x y)).subst lower) ≡
      [.request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩,
        .request .one fun (_ : Nat) =>
          .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (x + y) .nil)⟩] := .refl

/-! Two equal calls. -/

/-- The operands of `A`: the two inputs. -/
def addInputs : PortMap [(), ()] (sig.input Op.add) := .cons .here (.cons (.there .here) .nil)

/-- The rest after two calls of `A`. `D` has the outputs of the two calls. The exit has the
output of `D` and the output of the first call. -/
def afterTwo : (c c' : (sig.output Op.add).Case) → Diagram sig (c'.1 ++ (c.1 ++ [(), ()])) Two
  | ⟨_, .here⟩, ⟨_, .here⟩ =>
      .step ⟨.add, .cons (.there .here) (.cons .here .nil)⟩ fun
        | ⟨_, .here⟩ =>
            .exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there (.there .here)) .nil)⟩

/-- Two calls of `A` at the two inputs, and then the rest. -/
def twice : Diagram sig [(), ()] Two :=
  .step ⟨.add, addInputs⟩ fun c => .step ⟨.add, addInputs.weaken _⟩ fun c' => afterTwo c c'

/-- One call of `A`, and then the rest with the output of that call at the two places. -/
def once : Diagram sig [(), ()] Two :=
  .step ⟨.add, addInputs⟩ fun c => Diagram.rename (PortMap.copy c.1 _) (afterTwo c c)

/-- The copy rule relates the two diagrams. -/
def copied : Diagram.Copy twice once :=
  Diagram.Copy.copy (S := sig) Op.add .refl addInputs afterTwo

set_option smartUnfolding false in
/-- The two diagrams give the same two values, for arbitrary inputs. -/
def twiceRun (flag : Bool) (u v x y : Nat) :
    (observe stop count twice flag u v x y, observe stop count once flag u v x y) ≡
      ((x + y + (x + y), x + y), (x + y + (x + y), x + y)) := .refl

/-- The soundness of the copy rule: the two diagrams agree after the lowering. -/
def copySound (x y : Nat) :
    Free.Agreement ((twice.meaning stop count (inputs x y)).subst lower)
      ((once.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.Derivation.rule (R := Rules.copy sig) copied).sound stop count (.copy returns)
    (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the two diagrams is consumed through a dependent
payload that has the output of `D`. -/
def copyPayload (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((copySound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + y + (x + y), Nat.lt_succ_self _⟩).val ≡ x + y + (x + y) := .refl

/-- A rest after two calls of `A` that has two steps. `D` has the outputs of the two calls. The
effectful `C` has the output of `D`. The exit has the output of `D` and the response. -/
def afterLong : (c c' : (sig.output Op.add).Case) → Diagram sig (c'.1 ++ (c.1 ++ [(), ()])) Two
  | ⟨_, .here⟩, ⟨_, .here⟩ =>
      .step ⟨.add, .cons (.there .here) (.cons .here .nil)⟩ fun
        | ⟨_, .here⟩ =>
            .step ⟨.emit, .cons .here .nil⟩ fun
              | ⟨_, .here⟩ =>
                  .exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩

/-- Two calls of `A` at the two inputs, and then the rest with two steps. -/
def twiceLong : Diagram sig [(), ()] Two :=
  .step ⟨.add, addInputs⟩ fun c => .step ⟨.add, addInputs.weaken _⟩ fun c' => afterLong c c'

/-- One call of `A`, and then the rest with the output of that call at the two places. -/
def onceLong : Diagram sig [(), ()] Two :=
  .step ⟨.add, addInputs⟩ fun c => Diagram.rename (PortMap.copy c.1 _) (afterLong c c)

/-- The soundness of the copy rule for the rest with two steps. -/
def longSound (x y : Nat) :
    Free.Agreement ((twiceLong.meaning stop count (inputs x y)).subst lower)
      ((onceLong.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.Derivation.rule (R := Rules.copy sig)
      (Diagram.Copy.copy (S := sig) Op.add .refl addInputs afterLong)).sound stop count
    (.copy returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the two diagrams is consumed through a dependent
payload that has the response of the store. -/
def longPayload (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((longSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + (x + y + (x + y)), Nat.lt_succ_self _⟩).val ≡ u + (x + y + (x + y)) := .refl

/-- The diagram with two calls is a diagram of the fragment. -/
def twiceStraight : twice.Straight := ⟨oneCase, oneCase, oneCase, ()⟩

/-- The call of `A` at the histories of the two inputs. -/
def callA : Call sig [(), ()] Op.add :=
  .mk (.cons (.input .here) (.cons (.input (.there .here)) .nil)) none

/-- The call of `D`: its two operands have one history. -/
def callD : Call sig [(), ()] Op.add :=
  .mk (.cons (.output callA center .here) (.cons (.output callA center .here) .nil)) none

/-- The occurrence of each call of `A`. -/
def occA : sig.Occurrence [(), ()] := ⟨Op.add, callA⟩

/-- The occurrence of `D`. -/
def occD : sig.Occurrence [(), ()] := ⟨Op.add, callD⟩

/-- The occurrences of the diagram with two calls. -/
def twiceOccurrences : List (sig.Occurrence [(), ()]) := [occA, occA, occD]

set_option smartUnfolding false in
/-- The two calls of `A` are one occurrence two times in the graph of the diagram. -/
def twiceGraph : twice.graph twiceStraight ≡ twiceOccurrences := .refl

set_option smartUnfolding false in
/-- The list of the orders has the two orders of the two calls. -/
def twiceWords :
    ((Diagram.orders twice twiceStraight).map fun r =>
        Diagram.Order.depths r.1 twice r.2 twiceStraight) ≡
      [[0, 0, 0], [1, 0, 0]] := .refl

/-- The first run is one call of `A`: its operands are inputs. -/
def firstRun : (sig.admissible [(), ()]).Pre ((0 : Nat), ([occA, occA, occD], [])) :=
  ⟨(occA, [occA, occD]), .refl, fun | _, .here => () | _, .there .here => (), ()⟩

/-- The second run is `D`: each of its operands has the history of the call that is done. -/
def secondRun : (sig.admissible [(), ()]).Pre ((1 : Nat), ([occA, occD], [occA])) :=
  ⟨(occD, [occA]), .refl, fun | _, .here => .here | _, .there .here => .here, ()⟩

/-- The third run is the other call of `A`. -/
def thirdRun : (sig.admissible [(), ()]).Pre ((0 : Nat), ([occA], [occD, occA])) :=
  ⟨(occA, []), .refl, fun | _, .here => () | _, .there .here => (), ()⟩

/-- The word `[0, 1, 0]` runs one call of `A`, then `D`, and then the other call of `A`. It is
an admissible order of the occurrences. -/
def rewired :
    FreeDep (sig.admissible [(), ()]) (sig.Finished [(), ()])
      ((word [0, 1, 0]).thread (E := Empty) (twiceOccurrences, [])) :=
  Signature.ran (rest := word [1, 0]) 0 (twiceOccurrences, []) firstRun
    (Signature.ran (rest := word [0]) 1 ([occA, occD], [occA]) secondRun
      (Signature.ran (rest := word []) 0 ([occA], [occD, occA]) thirdRun
        (.pure (Identity.refl : ([] : List (sig.Occurrence [(), ()])) ≡ []))))

set_option smartUnfolding false in
/-- The run of that evidence on the machine gives the identity that no occurrence remains. The
identity is consumed through a dependent payload. -/
def rewiredFinished :
    (Identity.transport (fun (l : List (sig.Occurrence [(), ()])) => Fin (l.length + 1))
      (finished (machine.run (word [0, 1, 0]) (twiceOccurrences, []))
        (FreeDep.run machineEvidence rewired))
      ⟨0, Nat.zero_lt_succ _⟩).val ≡ 0 := .refl

/-- The interchange equation set with the copy equation set. -/
abbrev both : Rules sig := (Rules.interchange sig).sum (Rules.copy sig)

set_option smartUnfolding false in
/-- The merged diagram has one call of `A`: it has two steps, and the diagram with two calls has
three. -/
def mergedSize : (twice.size, (twice.merge twiceStraight).size) ≡ (3, 2) := .refl

set_option smartUnfolding false in
/-- The merged diagram gives the values of the diagram with two calls. -/
def mergedRun (flag : Bool) (u v x y : Nat) :
    observe stop count (twice.merge twiceStraight) flag u v x y ≡ (x + y + (x + y), x + y) :=
  .refl

/-- The soundness of the derivation of the merged diagram. -/
def mergedSound (x y : Nat) :
    Free.Agreement ((twice.meaning stop count (inputs x y)).subst lower)
      (((twice.merge twiceStraight).meaning stop count (inputs x y)).subst lower) :=
  (Diagram.mergeDerivation (R := both) (Rules.Map.inl _ _) (Rules.Map.inr _ _) twice
      twiceStraight).sound stop count (.sum (.interchange returns) (.copy returns))
    (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values of the diagram with two calls and of its merged diagram
is consumed through a dependent payload that has the output of `D`. -/
def mergedPayload (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((mergedSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + y + (x + y), Nat.lt_succ_self _⟩).val ≡ x + y + (x + y) := .refl

/-- The merged diagram of the diagram with two calls is a diagram of the fragment. -/
def mergedStraight : (twice.merge twiceStraight).Straight := twice.mergeStraight twiceStraight

set_option smartUnfolding false in
/-- The graph of the merged diagram has the occurrence of `A` one time. -/
def mergedGraph : (twice.merge twiceStraight).graph mergedStraight ≡ [occA, occD] := .refl

/-- No two occurrences of the graph of the merged diagram are equal. -/
def mergedDistinct : Elem.Distinct ((twice.merge twiceStraight).graph mergedStraight) :=
  Diagram.mergeDistinct twice twiceStraight mergedStraight

/-- The first run of the merged graph is the call of `A`. -/
def mergedFirst : (sig.admissible [(), ()]).Pre ((0 : Nat), ([occA, occD], [])) :=
  ⟨(occA, [occD]), .refl, fun | _, .here => () | _, .there .here => (), ()⟩

/-- The second run is `D`. -/
def mergedSecond : (sig.admissible [(), ()]).Pre ((0 : Nat), ([occD], [occA])) :=
  ⟨(occD, []), .refl, fun | _, .here => .here | _, .there .here => .here, ()⟩

/-- The word `[0, 0]` is an admissible order of the merged graph. -/
def mergedWord :
    FreeDep (sig.admissible [(), ()]) (sig.Finished [(), ()])
      ((word [0, 0]).thread (E := Empty) ([occA, occD], [])) :=
  Signature.ran (rest := word [0]) 0 ([occA, occD], []) mergedFirst
    (Signature.ran (rest := word []) 0 ([occD], [occA]) mergedSecond
      (.pure (Identity.refl : ([] : List (sig.Occurrence [(), ()])) ≡ [])))

/-- The theorem of the other direction gives an order of the merged diagram from that
evidence, with the evidence of the merge that no two occurrences are equal. -/
def mergedOrder :=
  Diagram.Order.ofGraph (twice.merge twiceStraight) mergedStraight mergedDistinct [0, 0]
    (Identity.transport
      (fun (g : List (sig.Occurrence [(), ()])) =>
        FreeDep (sig.admissible [(), ()]) (sig.Finished [(), ()])
          ((word [0, 0]).thread (E := Empty) (g, [])))
      mergedGraph.symm mergedWord)

set_option smartUnfolding false in
/-- That order has the two steps of the merged diagram. -/
def mergedOrderOps :
    Diagram.ops mergedOrder.1
        (Diagram.Order.straight mergedOrder.1 (twice.merge twiceStraight) mergedOrder.2.1
          mergedStraight) ≡
      [Op.add, Op.add] := .refl

set_option smartUnfolding false in
/-- The evidence of the merge gives the reflexivity proof at one position. -/
def mergedDistinctHere : mergedDistinct occA .here .here ≡ .refl := .refl

/-- A position in the graph of the diagram with two calls, from a position in the list of its
occurrences. -/
def inTwice {x : sig.Occurrence [(), ()]} (i : Elem x twiceOccurrences) :
    Elem x (twice.graph twiceStraight) :=
  Identity.transport (fun g => Elem x g) twiceGraph.symm i

set_option smartUnfolding false in
/-- The link gives each occurrence of the diagram with two calls its position in the graph of
the merged diagram. The two calls of `A` have one position. -/
def linkPositions :
    ((((twice.mergeLink twiceStraight mergedStraight).1 occA (inTwice .here)).toFin.val,
        ((twice.mergeLink twiceStraight mergedStraight).1 occA
          (inTwice (.there .here))).toFin.val),
      ((twice.mergeLink twiceStraight mergedStraight).1 occD
        (inTwice (.there (.there .here)))).toFin.val) ≡ ((0, 0), 1) := .refl

set_option smartUnfolding false in
/-- The occurrence of `A` in the graph of the merged diagram has the position of the first call
of `A` in the graph of the diagram. -/
def linkBack :
    ((twice.mergeLink twiceStraight mergedStraight).2 occA
      (Identity.transport (fun g => Elem occA g) mergedGraph.symm .here)).toFin.val ≡ 0 := .refl

/-- `A` at the two inputs, then the effectful `C` at the first input, and then `A` at the two
inputs again. The exit has the output of the second call of `A` and the response of `C`. -/
def apart : Diagram sig [(), ()] Two :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ fun
    | ⟨_, .here⟩ => .step ⟨.emit, .cons (.there .here) .nil⟩ fun
      | ⟨_, .here⟩ =>
          .step ⟨.add, .cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil)⟩
            fun
            | ⟨_, .here⟩ =>
                .exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩

/-- The diagram is a diagram of the fragment. -/
def apartStraight : apart.Straight := ⟨oneCase, oneCase, oneCase, ()⟩

set_option smartUnfolding false in
/-- The merged diagram has one call of `A`. -/
def apartSize : (apart.size, (apart.merge apartStraight).size) ≡ (3, 2) := .refl

set_option smartUnfolding false in
/-- The merged diagram gives the values of the diagram, for arbitrary inputs and an arbitrary
response of the store. -/
def apartRun (flag : Bool) (u v x y : Nat) :
    (observe stop count apart flag u v x y,
        observe stop count (apart.merge apartStraight) flag u v x y) ≡
      ((x + y, u + x), (x + y, u + x)) := .refl

/-- The soundness of the derivation of the merged diagram: the second call of `A` moves before
`C` by one interchange, and the copy rule gives one call. -/
def apartSound (x y : Nat) :
    Free.Agreement ((apart.meaning stop count (inputs x y)).subst lower)
      (((apart.merge apartStraight).meaning stop count (inputs x y)).subst lower) :=
  (Diagram.mergeDerivation (R := both) (Rules.Map.inl _ _) (Rules.Map.inr _ _) apart
      apartStraight).sound stop count (.sum (.interchange returns) (.copy returns))
    (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the returned values is consumed through a dependent payload that has the
response of the store. -/
def apartPayload (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((apartSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

end Draft.Checks.Dependency

/-- info: 'Draft.Checks.Dependency.orders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.orders

/-- info: 'Draft.Checks.Dependency.sourceRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.sourceRun

/-- info: 'Draft.Checks.Dependency.middleRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleRun

/-- info: 'Draft.Checks.Dependency.frontRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontRun

/-- info: 'Draft.Checks.Dependency.middleSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleSound

/-- info: 'Draft.Checks.Dependency.frontSound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontSound

/-- info: 'Draft.Checks.Dependency.readySteps' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.readySteps

/-- info: 'Draft.Checks.Dependency.allOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.allOrders

/-- info: 'Draft.Checks.Dependency.allRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.allRuns

/-- info: 'Draft.Checks.Dependency.frontSum' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontSum

/-- info: 'Draft.Checks.Dependency.diamondOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.diamondOrders

/-- info: 'Draft.Checks.Dependency.diamondRuns' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.diamondRuns

/-- info: 'Draft.Checks.Dependency.discardedOrders' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.discardedOrders

/-- info: 'Draft.Checks.Dependency.discardedCalls' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.discardedCalls

/-- info: 'Draft.Checks.Dependency.sourceReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.sourceReceipt

/-- info: 'Draft.Checks.Dependency.listedPositions' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.listedPositions

/-- info: 'Draft.Checks.Dependency.listedPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.listedPayload

/-- info: 'Draft.Checks.Dependency.middleReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleReceipt

/-- info: 'Draft.Checks.Dependency.frontReceipt' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontReceipt

/-- info: 'Draft.Checks.Dependency.keptC' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.keptC

/-- info: 'Draft.Checks.Dependency.keptBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.keptBack

/-- info: 'Draft.Checks.Dependency.keptRound' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.keptRound

/-- info: 'Draft.Checks.Dependency.notAdmissible' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.notAdmissible

/-- info: 'Draft.Checks.Dependency.frontGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontGraph

/-- info: 'Draft.Checks.Dependency.middleGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.middleGraph

/-- info: 'Draft.Checks.Dependency.movedPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.movedPayload

/-- info: 'Draft.Checks.Dependency.words' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.words

/-- info: 'Draft.Checks.Dependency.frontFinished' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontFinished

/-- info: 'Draft.Checks.Dependency.frontDone' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontDone

/-- info: 'Draft.Checks.Dependency.twiceRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.twiceRun

/-- info: 'Draft.Checks.Dependency.copyPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.copyPayload

/-- info: 'Draft.Checks.Dependency.longPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.longPayload

/-- info: 'Draft.Checks.Dependency.twiceGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.twiceGraph

/-- info: 'Draft.Checks.Dependency.twiceWords' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.twiceWords

/-- info: 'Draft.Checks.Dependency.rewiredFinished' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.rewiredFinished

/-- info: 'Draft.Checks.Dependency.mergedSize' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedSize

/-- info: 'Draft.Checks.Dependency.mergedRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedRun

/-- info: 'Draft.Checks.Dependency.mergedPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedPayload

/-- info: 'Draft.Checks.Dependency.apartSize' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.apartSize

/-- info: 'Draft.Checks.Dependency.apartRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.apartRun

/-- info: 'Draft.Checks.Dependency.apartPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.apartPayload

/-- info: 'Draft.Checks.Dependency.frontAgainOps' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontAgainOps

/-- info: 'Draft.Checks.Dependency.frontAgainWord' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.frontAgainWord

/-- info: 'Draft.Checks.Dependency.mergedGraph' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedGraph

/-- info: 'Draft.Checks.Dependency.mergedOrderOps' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedOrderOps

/-- info: 'Draft.Checks.Dependency.mergedDistinctHere' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.mergedDistinctHere

/-- info: 'Draft.Checks.Dependency.linkPositions' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.linkPositions

/-- info: 'Draft.Checks.Dependency.linkBack' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Dependency.linkBack
