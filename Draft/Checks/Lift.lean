import Draft.Verified
import Draft.Specification.Verified
import Draft.Checks.Diagram
import Draft.Checks.Countdown
import Draft.Checks.Specification
import Draft.Checks.Verified

/-! Verified diagrams with a step, a composite, a frame, and a loop.

Each group has a specification of the operations, a specification of the whole diagram, and the
lift of the diagram by its constructors. The lowering is a verified implementation, and the
composition of the two verified implementations has the specification of the store as its
assumption. A run with a provider that has evidence gives the evidence at the exit, and each
check eliminates that evidence, with arbitrary inputs, arbitrary responses of the store, and
the two admission constructors.

The first group has the two orders of a pure step and an effectful step. The interchange
derivation moves the lift of the first order to the second order.

The second group has one continuation of two control paths. The first diagram establishes a
condition on the sum at the boundary of the continuation, from the postcondition of the test in
each path, and the continuation receives it.

The third group has one effectful step of two control paths, in a frame. The exit of the
shared step has the receipt of the step, and the continuation of each path receives it with the
kept input. The frame equation moves the lift to the copairing that has the frame of each path
alone.

The fourth group has the loop that counts down. The family at its entrance has the receipts of
the calls of the earlier iterations, the identity of the value with the first value plus their
responses, and a count: the counter is less than the number of the unrollings that remain. A
witness of the precondition shows that the first counter is less than the number of
unrollings. A derivation with the interchange rule under the loop moves the verified
implementation to the loop that has the effectful step before the pure step in each
iteration, with the same specification and the same number of unrollings.

Each lift has the empty condition at the limit. The verified implementation thus has an
arbitrary computation at the limit, and it needs no evidence for that computation. The
diagrams with no loop have an arbitrary number of unrollings. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Lift

open Container
open Draft.Checks.Dependent (Admission Receipt expected)

/-- The value of a response with one port. -/
def valueOf : (Boundary.one [()]).At (fun _ : Unit => Nat) → Nat
  | ⟨⟨_, .here⟩, vals⟩ => vals.lookup .here

/-- The postcondition of a test for zero: the first case has the identity of the operand with
zero, and the second case has its predecessor. -/
def ZeroCase (x : Nat) : Boundary.Case ([[], []] : Boundary Unit) → Type
  | ⟨_, .here⟩ => x ≡ 0
  | ⟨_, .there _⟩ => (k : Nat) × (x ≡ k + 1)

end Draft.Checks.Lift

namespace Draft.Checks.Diagram

open Container
open Draft.Checks.Dependent (Admission Receipt expected)
open Draft.Checks.Lift (valueOf ZeroCase)

/-! The two orders of a pure step and an effectful step. -/

/-- The specification of each operation. The sum has its value, and the test has the fact of
its case. The effectful operation has an admission, and its response has a hidden response of
the store with a receipt for that admission. -/
def opSpec : DepPoly.{0, 0, 0, 0} (sig.interface Value) where
  Pre
    | ⟨.add, _⟩ => Unit
    | ⟨.isZero, _⟩ => Unit
    | ⟨.emit, _⟩ => Admission
  Post
    | ⟨.add, args⟩, _, resp => valueOf resp ≡ args.lookup .here + args.lookup (.there .here)
    | ⟨.isZero, args⟩, _, resp => ZeroCase (args.lookup .here) resp.1
    | ⟨.emit, args⟩, pre, resp =>
        (m : Nat) × ((valueOf resp ≡ m + args.lookup .here) × Receipt (expected pre m))

/-- The lowering is a verified implementation: each operation satisfies its specification,
with the specification of the store as the assumption on each call. -/
def lowerDep : ImplDep opSpec Verified.spec lower
  | ⟨.add, _⟩, _ => .pure .refl
  | ⟨.isZero, .cons 0 .nil⟩, _ => .pure (Identity.refl : (0 : Nat) ≡ 0)
  | ⟨.isZero, .cons (k + 1) .nil⟩, _ =>
      .pure (⟨k, .refl⟩ : (j : Nat) × (k + 1 ≡ j + 1))
  | ⟨.emit, _⟩, pre => .request pre fun (m : Nat) receipt => .pure ⟨m, .refl, receipt⟩

/-- The specification of the diagram of the two steps. The witness of its precondition is an
admission. The exit has the sum of the two inputs, and a receipt for that admission. -/
def wholeSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] [.one [(), ()]]) where
  Pre _ := Admission
  Post env pre out :=
    ((values out).1 ≡ env.lookup .here + env.lookup (.there .here)) ×
      ((m : Nat) × (((values out).2 ≡ m + env.lookup .here) × Receipt (expected pre m)))

/-- The lift of the first order, by the constructors of the diagram. The step of the sum needs
no admission. The effectful step takes the admission of the diagram. The exit has the
postcondition of the sum and the receipt of the effectful step. -/
def earlyLift (n : Nat) (env : All Value [(), ()]) (pre : wholeSpec.Pre env) :
    early.HoldsStill opSpec Empty n (wholeSpec.Post env pre) env :=
  Diagram.HoldsStill.step (S := sig) ⟨Op.add, addArgs⟩ _ () fun
    | ⟨⟨_, .here⟩, .cons _ .nil⟩, sum =>
        Diagram.HoldsStill.step (S := sig) ⟨Op.emit, emitArgs.weaken _⟩ _ pre fun
          | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt => Diagram.HoldsStill.exit _ ⟨sum, receipt⟩

variable (stop : Free (sig.interface Value) (Exits.At [.one [(), ()]] Value)) (count : Nat)

/-- The verified diagram and then the verified lowering: the composition of verified
implementations. -/
def loweredEarly : ImplDep wholeSpec Verified.spec ((early.impl stop count).trans lower) :=
  (Diagram.HoldsStill.impl (earlyLift count) fun _ _ e => e.elim).trans lowerDep

/-- The interchange as a map of verified implementations of one specification. -/
def loweredLate : ImplDep wholeSpec Verified.spec ((late.impl stop count).trans lower) :=
  interchange.lift (.interchange returns) stop count (loweredEarly stop count)

/-- The receipt at the exit, from a run with a provider that has evidence. -/
def consume {f : Impl (Diagram.interface Value [(), ()] [.one [(), ()]]) Free.store}
    (ff : ImplDep wholeSpec Verified.spec f) (flag : Bool) (u v x y : Nat) (pre : Admission) :
    Nat :=
  ((ff.run (Verified.verify flag u v)) (inputs x y) pre).2.2.2.read

set_option smartUnfolding false in
/-- The two admission constructors give different payloads, for arbitrary inputs and arbitrary
responses of the store. -/
def earlyFirst (flag : Bool) (u v x y key : Nat) :
    consume (loweredEarly stop count) flag u v x y (.first key) ≡ u + key := .refl

set_option smartUnfolding false in
def earlySecond (flag : Bool) (u v x y key : Nat) :
    consume (loweredEarly stop count) flag u v x y (.second key) ≡ key + u + 1 := .refl

set_option smartUnfolding false in
/-- After the interchange, the evidence of the second order gives the same payloads. -/
def lateFirst (flag : Bool) (u v x y key : Nat) :
    consume (loweredLate stop count) flag u v x y (.first key) ≡ u + key := .refl

set_option smartUnfolding false in
def lateSecond (flag : Bool) (u v x y key : Nat) :
    consume (loweredLate stop count) flag u v x y (.second key) ≡ key + u + 1 := .refl

set_option smartUnfolding false in
/-- The postcondition of the sum is consumed through a dependent payload. -/
def earlySum (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (((loweredEarly stop count).run (Verified.verify flag u v)) (inputs x y) pre).1
      ⟨x + y, Nat.lt_succ_self _⟩).val ≡ x + y := .refl

/-! One continuation of two control paths. -/

/-- The sum that the two paths give. -/
def pathSum : Nat → Nat → Nat
  | 0, y => y + y
  | x + 1, y => x + 1 + y

/-- The specification of the two forms. The exit has the sum of the path, and the response of
the effectful step with a receipt. -/
def sharedSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] [.one [(), ()]]) where
  Pre _ := Admission
  Post env pre out :=
    ((values out).1 ≡ pathSum (env.lookup .here) (env.lookup (.there .here))) ×
      ((m : Nat) × (((values out).2 ≡ m + (values out).1) × Receipt (expected pre m)))

/-- The condition at the boundary of the continuation: its port has the sum of the path. -/
abbrev SumIs (env : All Value [(), ()]) (a : (Boundary.one [()]).At Value) : Type :=
  valueOf a ≡ pathSum (env.lookup .here) (env.lookup (.there .here))

/-- The lift of the shared form. Each path establishes the condition from the postcondition of
the test and the postcondition of its sum. The continuation receives the condition, and it
takes the admission of the diagram. -/
def sharedLift (n : Nat) (env : All Value [(), ()]) (pre : sharedSpec.Pre env) :
    shared.HoldsStill opSpec Empty n (sharedSpec.Post env pre) env :=
  Diagram.HoldsStill.seq (S := sig) (SumIs env) branches after
    (Diagram.HoldsStill.step (S := sig) ⟨Op.isZero, .cons .here .nil⟩ _ () fun
      | ⟨⟨_, .here⟩, .nil⟩, zero =>
          Diagram.HoldsStill.step (S := sig)
            ⟨Op.add, .cons (.there .here) (.cons (.there .here) .nil)⟩ _ () fun
            | ⟨⟨_, .here⟩, .cons s .nil⟩, sum =>
                Diagram.HoldsStill.exit _
                  (Identity.transport (fun k => s ≡ pathSum k (env.lookup (.there .here)))
                    zero.symm sum)
      | ⟨⟨_, .there .here⟩, .nil⟩, succ =>
          Diagram.HoldsStill.step (S := sig) ⟨Op.add, .cons .here (.cons (.there .here) .nil)⟩ _ ()
            fun
            | ⟨⟨_, .here⟩, .cons s .nil⟩, sum =>
                Diagram.HoldsStill.exit _
                  (Identity.transport (fun k => s ≡ pathSum k (env.lookup (.there .here)))
                    succ.2.symm
                    (Identity.transport (fun k => s ≡ k + env.lookup (.there .here)) succ.2 sum)))
    fun
      | ⟨⟨_, .here⟩, .cons _ .nil⟩, mid =>
          Continuation.HoldsStill.copair _
            (Diagram.HoldsStill.step (S := sig) ⟨Op.emit, .cons .here .nil⟩ _ pre fun
              | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt => Diagram.HoldsStill.exit _ ⟨mid, receipt⟩)

section

variable (stop : Free (sig.interface Value) (Exits.At [.one [(), ()]] Value)) (count : Nat)

/-- The verified shared form and then the verified lowering. -/
def loweredShared : ImplDep sharedSpec Verified.spec ((shared.impl stop count).trans lower) :=
  (Diagram.HoldsStill.impl (sharedLift count) fun _ _ e => e.elim).trans lowerDep

/-- The evidence at the exit of the shared form, from a run with a provider that has
evidence. -/
def sharedEvidence (flag : Bool) (u v x y : Nat) (pre : Admission) :=
  ((loweredShared stop count).run (Verified.verify flag u v)) (inputs x y) pre

set_option smartUnfolding false in
/-- The receipt of the continuation, in each case of the test and for each admission
constructor. -/
def sharedZeroFirst (flag : Bool) (u v y key : Nat) :
    (sharedEvidence stop count flag u v 0 y (.first key)).2.2.2.read ≡ u + key := .refl

set_option smartUnfolding false in
def sharedSuccSecond (flag : Bool) (u v x y key : Nat) :
    (sharedEvidence stop count flag u v (x + 1) y (.second key)).2.2.2.read ≡
      key + u + 1 := .refl

set_option smartUnfolding false in
/-- The condition at the boundary is consumed through a dependent payload, in each case of the
test. -/
def sharedZeroSum (flag : Bool) (u v y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (sharedEvidence stop count flag u v 0 y pre).1
      ⟨y + y, Nat.lt_succ_self _⟩).val ≡ y + y := .refl

set_option smartUnfolding false in
def sharedSuccSum (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (sharedEvidence stop count flag u v (x + 1) y pre).1
      ⟨x + 1 + y, Nat.lt_succ_self _⟩).val ≡ x + 1 + y := .refl

end

/-! One step of two control paths, in a frame. -/

/-- The specification of the framed form. The exit has the response of the shared step on the
first input, with a receipt. -/
def framedSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] [.one [(), ()]]) where
  Pre _ := Admission
  Post env pre out :=
    (m : Nat) × (((values out).2 ≡ m + env.lookup .here) × Receipt (expected pre m))

/-- The first port of a case of the entry of the frame. -/
def firstOf : paths.At Value → Nat
  | ⟨⟨_, .here⟩, vals⟩ => vals.lookup .here
  | ⟨⟨_, .there .here⟩, vals⟩ => vals.lookup .here

/-- The condition at the exit of the shared step: its response, with a receipt. -/
abbrev Receipted (pre : Admission) (x : Nat) (out : (Boundary.one [()]).At Value) : Type :=
  (m : Nat) × ((valueOf out ≡ m + x) × Receipt (expected pre m))

/-- The lift of the framed form. The test establishes that the first port of the entry is the
first input. The shared step takes the admission of the diagram, and the continuation of each
path receives the receipt with the kept input. -/
def framedLift (n : Nat) (env : All Value [(), ()]) (pre : framedSpec.Pre env) :
    framed.HoldsStill opSpec Empty n (framedSpec.Post env pre) env :=
  Diagram.HoldsStill.seq (S := sig) (fun a => firstOf a ≡ env.lookup .here) tested
    (.frame (M := bypass) keep enter call (.copair afterCall))
    (Diagram.HoldsStill.step (S := sig) ⟨Op.isZero, .cons .here .nil⟩ _ () fun
      | ⟨⟨_, .here⟩, .nil⟩, _ => Diagram.HoldsStill.exit _ .refl
      | ⟨⟨_, .there .here⟩, .nil⟩, _ => Diagram.HoldsStill.exit _ .refl)
    fun
      | ⟨⟨_, .here⟩, .cons x (.cons _ .nil)⟩, same =>
          Continuation.HoldsStill.frame (S := sig) (M := bypass) (Receipted pre x) keep enter call
            (.copair afterCall)
            (Diagram.HoldsStill.step (S := sig) ⟨Op.emit, .cons .here .nil⟩ _ pre fun
              | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt => Diagram.HoldsStill.exit _ receipt)
            fun
              | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt =>
                  Continuation.HoldsStill.copair _
                    (Diagram.HoldsStill.step (S := sig)
                      ⟨Op.add, .cons .here (.cons (.there .here) .nil)⟩ _ () fun
                      | ⟨⟨_, .here⟩, .cons _ .nil⟩, _ =>
                          Diagram.HoldsStill.exit _
                            ⟨receipt.1,
                              receipt.2.1.trans (Identity.cong (fun k => receipt.1 + k) same),
                              receipt.2.2⟩)
      | ⟨⟨_, .there .here⟩, .cons x (.cons _ .nil)⟩, same =>
          Continuation.HoldsStill.frame (S := sig) (M := bypass) (Receipted pre x) keep enter call
            (.copair afterCall)
            (Diagram.HoldsStill.step (S := sig) ⟨Op.emit, .cons .here .nil⟩ _ pre fun
              | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt => Diagram.HoldsStill.exit _ receipt)
            fun
              | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt =>
                  Continuation.HoldsStill.copair _
                    (Diagram.HoldsStill.step (S := sig)
                      ⟨Op.add, .cons (.there .here) (.cons (.there .here) .nil)⟩ _ () fun
                      | ⟨⟨_, .here⟩, .cons _ .nil⟩, _ =>
                          Diagram.HoldsStill.exit _
                            ⟨receipt.1,
                              receipt.2.1.trans (Identity.cong (fun k => receipt.1 + k) same),
                              receipt.2.2⟩)

section

variable (stop : Free (sig.interface Value) (Exits.At [.one [(), ()]] Value)) (count : Nat)

/-- The verified framed form and then the verified lowering. -/
def loweredFramed : ImplDep framedSpec Verified.spec ((framed.impl stop count).trans lower) :=
  (Diagram.HoldsStill.impl (framedLift count) fun _ _ e => e.elim).trans lowerDep

/-- The evidence at the exit of the framed form. -/
def framedEvidence (flag : Bool) (u v x y : Nat) (pre : Admission) :=
  ((loweredFramed stop count).run (Verified.verify flag u v)) (inputs x y) pre

set_option smartUnfolding false in
/-- The receipt of the shared step, after the continuation of each path. -/
def framedZeroFirst (flag : Bool) (u v y key : Nat) :
    (framedEvidence stop count flag u v 0 y (.first key)).2.2.read ≡ u + key := .refl

set_option smartUnfolding false in
def framedSuccSecond (flag : Bool) (u v x y key : Nat) :
    (framedEvidence stop count flag u v (x + 1) y (.second key)).2.2.read ≡
      key + u + 1 := .refl

set_option smartUnfolding false in
/-- The identity of the response is consumed through a dependent payload. It goes through the
condition at the entry of the frame. -/
def framedSuccResponse (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (framedEvidence stop count flag u v (x + 1) y pre).2.1
      ⟨u + (x + 1), Nat.lt_succ_self _⟩).val ≡ u + (x + 1) := .refl

/-- The frame equation as a map of verified implementations of one specification: the verified
form with the frame of each path alone. -/
def loweredEach : ImplDep framedSpec Verified.spec ((framedEach.impl stop count).trans lower) :=
  unshare.lift (.control returns) stop count (loweredFramed stop count)

/-- The evidence at the exit of the form with the frame of each path alone. -/
def eachEvidence (flag : Bool) (u v x y : Nat) (pre : Admission) :=
  ((loweredEach stop count).run (Verified.verify flag u v)) (inputs x y) pre

set_option smartUnfolding false in
/-- After the frame equation, the evidence gives the same payloads. -/
def eachZeroFirst (flag : Bool) (u v y key : Nat) :
    (eachEvidence stop count flag u v 0 y (.first key)).2.2.read ≡ u + key := .refl

set_option smartUnfolding false in
def eachSuccSecond (flag : Bool) (u v x y key : Nat) :
    (eachEvidence stop count flag u v (x + 1) y (.second key)).2.2.read ≡
      key + u + 1 := .refl

set_option smartUnfolding false in
def eachSuccResponse (flag : Bool) (u v x y : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1))
      (eachEvidence stop count flag u v (x + 1) y pre).2.1
      ⟨u + (x + 1), Nat.lt_succ_self _⟩).val ≡ u + (x + 1) := .refl

end

end Draft.Checks.Diagram

namespace Draft.Checks.Countdown

open Container
open Draft.Checks.Dependent (Admission Receipt expected)
open Draft.Checks.Lift (valueOf ZeroCase)
open Draft.Checks.Specification.Bound (Below)
open Draft.Checks.Specification.Interchange (countdownLate swap returns)

/-! The loop that counts down. -/

/-- The specification of each operation. The test has the fact of its case, and the
predecessor has its value. The effectful operation has an admission, and its response has a
hidden response of the store with a receipt for that admission. -/
def spec : DepPoly.{0, 0, 0, 0} (sig.interface Value) where
  Pre
    | ⟨.isZero, _⟩ => Unit
    | ⟨.pred, _⟩ => Unit
    | ⟨.emit, _⟩ => Admission
  Post
    | ⟨.isZero, args⟩, _, resp => ZeroCase (args.lookup .here) resp.1
    | ⟨.pred, args⟩, _, resp => valueOf resp ≡ (args.lookup .here).pred
    | ⟨.emit, args⟩, pre, resp =>
        (m : Nat) × ((valueOf resp ≡ m + args.lookup .here) × Receipt (expected pre m))

/-- The lowering is a verified implementation. -/
def lowerDep : ImplDep spec Verified.spec lower
  | ⟨.isZero, .cons 0 .nil⟩, _ => .pure (Identity.refl : (0 : Nat) ≡ 0)
  | ⟨.isZero, .cons (k + 1) .nil⟩, _ =>
      .pure (⟨k, .refl⟩ : (j : Nat) × (k + 1 ≡ j + 1))
  | ⟨.pred, _⟩, _ => .pure .refl
  | ⟨.emit, _⟩, pre => .request pre fun (m : Nat) receipt => .pure ⟨m, .refl, receipt⟩

/-- The receipts of the calls of the store, with the last call first. -/
abbrev Trace (pre : Admission) : Type := List ((m : Nat) × Receipt (expected pre m))

/-- A first value plus the responses of the calls. -/
def total {pre : Admission} : Trace pre → Nat → Nat
  | [], a => a
  | e :: tr, a => e.1 + total tr a

/-- The specification of the loop from the two inputs, with a number of unrollings. A witness of
the precondition is an admission, with the evidence that the counter is less than that number.
The exit has the receipts of the calls, and its value is the second input plus their
responses. -/
def countSpec (n : Nat) : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] [Out]) where
  Pre env := Admission × Below (env.lookup .here) n
  Post env pre x := (tr : Trace pre.1) × (result x ≡ total tr (env.lookup (.there .here)))

/-- The counter at an entrance of the loop. -/
def counterAt : Entry.At Value → Nat
  | ⟨⟨_, .here⟩, vals⟩ => vals.lookup .here

/-- The value at an entrance of the loop. -/
def valueAt : Entry.At Value → Nat
  | ⟨⟨_, .here⟩, vals⟩ => vals.lookup (.there .here)

/-- The invariant of the loop: the receipts of the calls of the earlier iterations, and the
identity of the value at the entrance with the first value plus their responses. -/
abbrev Invariant (pre : Admission) (first : Nat) (a : Entry.At Value) : Type :=
  (tr : Trace pre) × (valueAt a ≡ total tr first)

/-- The family with a count: the invariant, and the evidence that the counter at the entrance
is less than the count. -/
abbrev Counted (pre : Admission) (first : Nat) (m : Nat) (a : Entry.At Value) : Type :=
  Invariant pre first a × Below (counterAt a) m

/-- The lift of the body. At zero, the body exits with the invariant. At a successor, the
effectful step takes the admission of the diagram, and the exit to the entrance has the
invariant with one more receipt. The postconditions of the test and of the predecessor show
that the next counter is less than the count that is one less. -/
def bodyLift (n : Nat) (pre : Admission) (first : Nat) : (m : Nat) → (k : Entry.At Value) →
    Counted pre first (m + 1) k →
    body.HoldsStill spec Empty n
      (Exits.At.elim (Counted pre first m)
        (fun x => (tr : Trace pre) × (result x ≡ total tr first))) k
  | m, ⟨⟨_, .here⟩, .cons _ (.cons _ .nil)⟩, v =>
      Continuation.HoldsStill.copair _
        (Diagram.HoldsStill.step (S := sig) ⟨Op.isZero, .cons .here .nil⟩ _ () fun
          | ⟨⟨_, .here⟩, .nil⟩, _ => Diagram.HoldsStill.exit _ v.1
          | ⟨⟨_, .there .here⟩, .nil⟩, succ =>
              Diagram.HoldsStill.step (S := sig) ⟨Op.pred, .cons .here .nil⟩ _ () fun
                | ⟨⟨_, .here⟩, .cons _ .nil⟩, isPred =>
                    Diagram.HoldsStill.step (S := sig)
                      ⟨Op.emit, .cons (.there (.there .here)) .nil⟩ _ pre fun
                      | ⟨⟨_, .here⟩, .cons _ .nil⟩, receipt =>
                          Diagram.HoldsStill.exit _
                            (⟨⟨receipt.1, receipt.2.2⟩ :: v.1.1,
                                receipt.2.1.trans
                                  (Identity.cong (fun k => receipt.1 + k) v.1.2)⟩,
                              Identity.transport (fun j => Below j m)
                                (isPred.trans (Identity.cong Nat.pred succ.2)).symm
                                (Identity.transport (fun j => Below j (m + 1)) succ.2 v.2).pred))

/-- The lift of the loop from the two inputs. The exit to the entrance has the invariant with
no receipt, and the evidence of the precondition that the counter is less than the number of
unrollings. -/
def countdownLift (n : Nat) (env : All Value [(), ()]) (pre : (countSpec n).Pre env) :
    countdown.HoldsStill spec Empty n ((countSpec n).Post env pre) env :=
  Diagram.HoldsStill.seq (S := sig) (Counted pre.1 (env.lookup (.there .here)) n) enter loop
    (Diagram.HoldsStill.exit _ (⟨[], .refl⟩, pre.2))
    fun _ start =>
      Continuation.HoldsStill.loopCounted (S := sig) (Counted pre.1 (env.lookup (.there .here)))
        body (bodyLift n pre.1 (env.lookup (.there .here))) (fun _ v => v.2.zero) start

variable (stop : Free (sig.interface Value) (Exits.At [Out] Value))

/-- The verified loop and then the verified lowering, for a number of unrollings. -/
def lowered (n : Nat) :
    ImplDep (countSpec n) Verified.spec ((countdown.impl stop n).trans lower) :=
  (Diagram.HoldsStill.impl (countdownLift n) fun _ _ e => e.elim).trans lowerDep

/-- The evidence at the exit from the counter 2, with three or more unrollings. -/
def evidence (n : Nat) (flag : Bool) (u v a : Nat) (pre : Admission) :=
  ((lowered stop (n + 3)).run (Verified.verify flag u v)) (inputs 2 a) (pre, ⟨n, .refl⟩)

set_option smartUnfolding false in
/-- The invariant has the responses of the two calls, for an arbitrary value and arbitrary
responses of the store. -/
def traceResponses (n : Nat) (flag : Bool) (u v a : Nat) (pre : Admission) :
    (evidence stop n flag u v a pre).1.map (fun e => e.1) ≡ [u, u] := .refl

set_option smartUnfolding false in
/-- Each receipt of the invariant has the payload of its admission constructor. -/
def traceFirst (n : Nat) (flag : Bool) (u v a key : Nat) :
    (evidence stop n flag u v a (.first key)).1.map (fun e => e.2.read) ≡
      [u + key, u + key] := .refl

set_option smartUnfolding false in
def traceSecond (n : Nat) (flag : Bool) (u v a key : Nat) :
    (evidence stop n flag u v a (.second key)).1.map (fun e => e.2.read) ≡
      [key + u + 1, key + u + 1] := .refl

set_option smartUnfolding false in
/-- The identity of the value at the exit is consumed through a dependent payload. -/
def traceTotal (n : Nat) (flag : Bool) (u v a : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1)) (evidence stop n flag u v a pre).2
      ⟨u + (u + a), Nat.lt_succ_self _⟩).val ≡ u + (u + a) := .refl

/-! The verified loop along a derivation. The derivation has the interchange rule under the
loop, and the rule holds after the substitution of the lowering. The verified implementation
from the family with a count moves to the loop that has the effectful step before the pure
step in each iteration. No constructor gives the evidence of that loop. -/

/-- The verified implementation of the second loop, along the derivation. -/
def loweredLate (n : Nat) :
    ImplDep (countSpec n) Verified.spec ((countdownLate.impl stop n).trans lower) :=
  swap.lift (.interchange returns) stop n (lowered stop n)

/-- The evidence at the exit of the second loop from the counter 2, with three or more
unrollings. -/
def evidenceLate (n : Nat) (flag : Bool) (u v a : Nat) (pre : Admission) :=
  ((loweredLate stop (n + 3)).run (Verified.verify flag u v)) (inputs 2 a) (pre, ⟨n, .refl⟩)

set_option smartUnfolding false in
/-- After the derivation, each receipt has the payload of its admission constructor. -/
def lateTraceSecond (n : Nat) (flag : Bool) (u v a key : Nat) :
    (evidenceLate stop n flag u v a (.second key)).1.map (fun e => e.2.read) ≡
      [key + u + 1, key + u + 1] := .refl

set_option smartUnfolding false in
/-- After the derivation, the identity of the value at the exit is consumed through a
dependent payload. -/
def lateTraceTotal (n : Nat) (flag : Bool) (u v a : Nat) (pre : Admission) :
    (Identity.transport (fun k => Fin (k + 1)) (evidenceLate stop n flag u v a pre).2
      ⟨u + (u + a), Nat.lt_succ_self _⟩).val ≡ u + (u + a) := .refl

end Draft.Checks.Countdown

/-- info: 'Draft.Checks.Diagram.lateSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.lateSecond

/-- info: 'Draft.Checks.Diagram.earlySum' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.earlySum

/-- info: 'Draft.Checks.Diagram.sharedSuccSum' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.sharedSuccSum

/-- info: 'Draft.Checks.Diagram.framedSuccResponse' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.framedSuccResponse

/-- info: 'Draft.Checks.Diagram.eachSuccSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.eachSuccSecond

/-- info: 'Draft.Checks.Diagram.eachSuccResponse' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.eachSuccResponse

/-- info: 'Draft.Checks.Countdown.traceSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Countdown.traceSecond

/-- info: 'Draft.Checks.Countdown.traceTotal' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Countdown.traceTotal

/-- info: 'Draft.Checks.Countdown.lateTraceSecond' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Countdown.lateTraceSecond

/-- info: 'Draft.Checks.Countdown.lateTraceTotal' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Countdown.lateTraceTotal
