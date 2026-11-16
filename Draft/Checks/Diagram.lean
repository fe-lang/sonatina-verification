import Draft.Diagram
import Draft.Checks.Free

/-! Diagrams with a pure operation, a pure test, and an effectful operation.

The first group has one pure operation with two inputs and one effectful operation, in the two
orders of the two steps. The first input has two uses. An interchange derivation relates the
two diagrams. After the substitution of the implementations, the two orders are one
computation with one call, for arbitrary inputs. A diagram with other functions of the case
agrees with the first diagram of the rule, and the derivation starts from it too. A derivation
in the control equation set relates an exit to the boundary of a continuation, after the two
steps, to the rest with renamed ports.

The first group also has a check with arbitrary inputs for each construction of a derivation:
the two premises of the interchange rule, the symmetry, the congruences, and the laws of
renaming.

The next group has one pure operation and two effectful operations. Two interchanges move the
pure step after the two effectful steps, and the symmetry of the relation moves it back. The
check of that derivation has closed inputs, and only the kernel reduces it.

The third group has a test, a different sum in each case, and one exit case for the two
paths. The continuation is one effectful step. The composite and the diagram with the
continuation at each exit give the same values in each case of the test, and the composite has
one step less.

The fourth group has a composite in a composite. One path of the inner composite exits past
the inner continuation, to the outer continuation. The outer composite and the diagram with
the outer continuation at each exit of the inner composite give the same values in each case
of the test.

The fifth group has a test, one effectful step for the two paths, and a different sum after
that step on each path. A frame has the one copy of the step, and its bypass keeps the path
and one input. The frame and the diagram with a copy of the step in each path give the same
values in each case of the test, and the frame has one step less.

The last group has two tests and three paths. A frame has one copy of the effectful step for
two of the paths. The third path exits past the frame, and its computation has no call. A
derivation in the control equation set relates an exit past the frame to the exit.

The diagrams of this module have no loop. Each check has an arbitrary number of unrollings and
an arbitrary computation at the limit of a loop.

Each check sets `smartUnfolding false`. The definitions of the diagrams keep the default. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Diagram

open Container
open Draft.Checks.Free (store provider)

inductive Op where
  | add
  | isZero
  | emit

/-- One value type. `add` is pure and has two inputs. `isZero` is a pure test: its output
boundary has two cases with no port. `emit` is effectful. -/
def sig : Signature Unit where
  Op := Op
  kind
    | .add => .pure
    | .isZero => .pure
    | .emit => .effectful
  input
    | .add => [(), ()]
    | .isZero => [()]
    | .emit => [()]
  output
    | .add => .one [()]
    | .isZero => [[], []]
    | .emit => .one [()]

abbrev Value : Unit → Type := fun _ => Nat

/-- `add` and `isZero` return without a call. The first case of `isZero` is the case of zero.
`emit` is one call of the store, and its response has the operand. -/
def lower : Impl (sig.interface Value) store
  | ⟨.add, args⟩ =>
      .pure ⟨Boundary.only _, .cons (args.lookup .here + args.lookup (.there .here)) .nil⟩
  | ⟨.isZero, args⟩ =>
      match args.lookup .here with
      | 0 => .pure ⟨⟨_, .here⟩, .nil⟩
      | _ + 1 => .pure ⟨⟨_, .there .here⟩, .nil⟩
  | ⟨.emit, args⟩ =>
      .request .one fun (n : Nat) => .pure ⟨Boundary.only _, .cons (n + args.lookup .here) .nil⟩

def inputs (x y : Nat) : All Value [(), ()] := .cons x (.cons y .nil)

/-- The two values of the one exit case. -/
def values : Exits.At [.one [(), ()]] Value → Nat × Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => (out.lookup .here, out.lookup (.there .here))

/-- A computation at the limit of a loop, for the checks with closed inputs. -/
def limit : Free (sig.interface Value) (Exits.At [.one [(), ()]] Value) :=
  .pure ⟨_, .here, Boundary.only _, .cons 0 (.cons 0 .nil)⟩

variable (stop : Free (sig.interface Value) (Exits.At [.one [(), ()]] Value)) (count : Nat)

/-- The two values at the exit of a run, with arbitrary responses of the store. -/
def observe (d : Diagram sig [(), ()] [.one [(), ()]]) (flag : Bool) (u v x y : Nat) :
    Nat × Nat :=
  values (((d.meaning (X := Value) stop count (inputs x y)).subst lower).run (provider flag u v))

/-! The two orders of a pure step and an effectful step. -/

/-- The exit with the sum and the response. The context has the response, the sum, and the
two inputs. -/
def done : Diagram sig [(), (), (), ()] [.one [(), ()]] :=
  .exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩

/-- The operands of the sum: the two inputs. -/
def addArgs : PortMap [(), ()] [(), ()] := .cons .here (.cons (.there .here) .nil)

/-- The operand of the effectful step: the first input, which the sum uses too. -/
def emitArgs : PortMap [(), ()] [()] := .cons .here .nil

/-- The rest after the two steps, for each pair of their output cases. -/
def rest : (ca : (sig.output .add).Case) → (cb : (sig.output .emit).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [(), ()])) [.one [(), ()]]
  | ⟨_, .here⟩, ⟨_, .here⟩ => done

/-- The pure step, and then the effectful step. The context of the effectful step has the
sum. -/
def early : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.add, addArgs⟩ fun ca => .step ⟨.emit, emitArgs.weaken _⟩ fun cb => rest ca cb

/-- The effectful step, and then the pure step. The rest has the two outputs exchanged. -/
def late : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.emit, emitArgs⟩ fun cb => .step ⟨.add, addArgs.weaken _⟩ fun ca =>
    (rest ca cb).rename (PortMap.exchange _ _ _)

/-- The effectful step, and then the pure step, with an exit that exchanges the two outputs
and a continuation. -/
def lateExit : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.emit, emitArgs⟩ fun cb => .step ⟨.add, addArgs.weaken _⟩ fun ca =>
    .seq (.exit (Exits.At.here ⟨Boundary.only _, PortMap.exchange _ _ _⟩)) (.one (rest ca cb))

/-- The effectful step, and then the pure step, with one exit. -/
def lateDirect : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.emit, .cons .here .nil⟩ (.one
    (.step ⟨.add, .cons (.there .here) (.cons (.there (.there .here)) .nil)⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))))

/-- The interchange derivation of the pure step. -/
def interchange : Diagram.Derivation (.interchange sig) early late :=
  .rule (.swap (S := sig) Op.add Op.emit (.inl .refl) addArgs emitArgs rest)

/-- The derivation in the other direction: the pure step moves before the effectful step. -/
def interchangeBack : Diagram.Derivation (.interchange sig) late early := .symm interchange

/-- The first exit equation of the control sum for the rest after the two steps: the exit to
the boundary of the continuation, and then the continuation, are the rest with renamed
ports. -/
def exitRule (ca : (sig.output Op.add).Case) (cb : (sig.output Op.emit).Case) :
    Diagram.Derivation (.control sig)
      (.seq (.exit (Exits.At.here ⟨Boundary.only _, PortMap.exchange _ _ _⟩)) (.one (rest ca cb)))
      ((rest ca cb).rename (PortMap.exchange _ _ _)) :=
  .rule (Sum.inr (Sum.inl (.exit (Boundary.only _) (PortMap.exchange _ _ _)
    (Boundary.family (F := fun Δ => Diagram sig Δ [.one [(), ()]]) (.cons (rest ca cb) .nil)))))

/-- The rule after the two steps, by the congruence of a step. -/
def exitDerivation : Diagram.Derivation (.control sig) lateExit late :=
  Diagram.Derivation.step (R := Rules.control sig) (Γ := [(), ()]) ⟨Op.emit, emitArgs⟩ fun cb =>
    Diagram.Derivation.step (R := Rules.control sig) ⟨Op.add, addArgs.weaken _⟩ fun ca =>
      exitRule ca cb

/-- The early order with the family of one case at each step, as a frontend writes it. It is
not the first diagram of the rule: its families are other functions of the case. -/
def earlyHand : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ (.one
    (.step ⟨.emit, .cons (.there .here) .nil⟩ (.one done)))

/-- It agrees with the first diagram of the rule: the families agree at each case. -/
def handAgreement : Diagram.Agreement earlyHand early :=
  .step _ fun
    | ⟨_, .here⟩ => .step _ fun
        | ⟨_, .here⟩ => .refl done

/-- The interchange derivation from the hand-written diagram. -/
def interchangeHand : Diagram.Derivation (.interchange sig) earlyHand late :=
  .trans (.agree handAgreement) interchange

/-- The agreement of the two computations, after the substitution. -/
def handMeaning (x y : Nat) :
    Free.Agreement ((earlyHand.meaning stop count (inputs x y)).subst lower)
      ((early.meaning stop count (inputs x y)).subst lower) :=
  (handAgreement.run stop count (inputs x y) fun r => Free.Agreement.refl (.pure r)).subst
    (Impl.Agreement.refl lower)

set_option smartUnfolding false in
/-- The identity of the two returned values, from the agreement of the diagrams, is consumed
through a dependent payload. -/
def handRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((handMeaning stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + y, Nat.lt_succ_self _⟩).val ≡ x + y := .refl

/-- `add` and `isZero` return without a call. -/
def returns : sig.Returns lower
  | .add, _, args =>
      ⟨⟨Boundary.only _, .cons (args.lookup .here + args.lookup (.there .here)) .nil⟩,
        .pure .refl⟩
  | .isZero, _, .cons 0 .nil => ⟨⟨⟨_, .here⟩, .nil⟩, .pure .refl⟩
  | .isZero, _, .cons (_ + 1) .nil => ⟨⟨⟨_, .there .here⟩, .nil⟩, .pure .refl⟩

/-- The soundness of the rule gives the agreement of the two orders. -/
def interchangeSound (x y : Nat) :
    Free.Agreement ((early.meaning stop count (inputs x y)).subst lower)
      ((late.meaning stop count (inputs x y)).subst lower) :=
  interchange.sound stop count (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The identity of the two returned values, from the soundness of the rule, is consumed
through a dependent payload that has the response of the store. -/
def interchangeRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((interchangeSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- The soundness of the derivation from the hand-written diagram. -/
def handSound (x y : Nat) :
    Free.Agreement ((earlyHand.meaning stop count (inputs x y)).subst lower)
      ((late.meaning stop count (inputs x y)).subst lower) :=
  interchangeHand.sound stop count (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
def handSoundRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((handSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- The soundness of the derivation in the control equation set. -/
def exitSound (x y : Nat) :
    Free.Agreement ((lateExit.meaning stop count (inputs x y)).subst lower)
      ((late.meaning stop count (inputs x y)).subst lower) :=
  exitDerivation.sound stop count (.control returns) (inputs x y) .pure

set_option smartUnfolding false in
def exitSoundRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((exitSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- The continuation that keeps the first value of the exit. -/
def firstOnly : Continuation sig (.one [(), ()]) [.one [()]] :=
  .copair (Boundary.family (F := fun Δ => Diagram sig Δ [.one [()]])
    (.cons (.exit ⟨_, .here, Boundary.only _, .cons .here .nil⟩) .nil))

/-- The exits of the first diagram of the composite: the boundary of the continuation, and
the boundary of the composite. -/
abbrev Open : Exits Unit := [.one [(), ()], .one [()]]

/-- The rest after the two steps: the exit to the boundary of the continuation, with the sum
and the response. -/
def restOpen : (ca : (sig.output .add).Case) → (cb : (sig.output .emit).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [(), ()])) Open
  | ⟨_, .here⟩, ⟨_, .here⟩ => .exit ⟨_, .here, ⟨_, .here⟩, .cons (.there .here) (.cons .here .nil)⟩

/-- The pure step, and then the effectful step, as the first diagram of a composite. -/
def earlyOpen : Diagram sig [(), ()] Open :=
  .step ⟨.add, addArgs⟩ fun ca => .step ⟨.emit, emitArgs.weaken _⟩ fun cb => restOpen ca cb

/-- The effectful step, and then the pure step, as the first diagram of a composite. -/
def lateOpen : Diagram sig [(), ()] Open :=
  .step ⟨.emit, emitArgs⟩ fun cb => .step ⟨.add, addArgs.weaken _⟩ fun ca =>
    (restOpen ca cb).rename (PortMap.exchange _ _ _)

/-- The interchange in a composite, by the congruence of a composite and of a copairing. -/
def composite :
    Diagram.Derivation (.interchange sig) (.seq earlyOpen firstOnly) (.seq lateOpen firstOnly) :=
  .seq (.rule (.swap (S := sig) Op.add Op.emit (.inl .refl) addArgs emitArgs restOpen))
    (.copair fun _ => .agree (.refl _))

/-- The one value of the exit of the composite. -/
def single : Exits.At [.one [()]] Value → Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => out.lookup .here

def compositeSound (stop : Free (sig.interface Value) (Exits.At [.one [()]] Value))
    (count : Nat) (x y : Nat) :
    Free.Agreement (((Diagram.seq earlyOpen firstOnly).meaning stop count (inputs x y)).subst lower)
      (((Diagram.seq lateOpen firstOnly).meaning stop count (inputs x y)).subst lower) :=
  composite.sound stop count (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
def compositeRun (stop : Free (sig.interface Value) (Exits.At [.one [()]] Value))
    (count : Nat) (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong single
        ((compositeSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + y, Nat.lt_succ_self _⟩).val ≡ x + y := .refl

set_option smartUnfolding false in
/-- The soundness of the derivation in the other direction, by the symmetry of the relation. -/
def backRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((interchangeBack.sound stop count (.interchange returns) (inputs x y) .pure).run
          (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- The exit with the sum and the response. The context has the sum, the response, and the
two inputs. -/
def restSecond : (ca : (sig.output Op.emit).Case) → (cb : (sig.output Op.add).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [(), ()])) [.one [(), ()]]
  | ⟨_, .here⟩, ⟨_, .here⟩ =>
      .exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩

/-- The effectful step, and then the pure step. -/
def emitFirst : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨Op.emit, emitArgs⟩ fun ca => .step ⟨Op.add, addArgs.weaken _⟩ fun cb =>
    restSecond ca cb

/-- The pure step, and then the effectful step. -/
def addFirst : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨Op.add, addArgs⟩ fun cb => .step ⟨Op.emit, emitArgs.weaken _⟩ fun ca =>
    (restSecond ca cb).rename (PortMap.exchange _ _ _)

/-- The interchange of the rule whose second step is the pure step. -/
def pureSecond : Diagram.Derivation (.interchange sig) emitFirst addFirst :=
  .rule (.swap (S := sig) Op.emit Op.add (.inr .refl) emitArgs addArgs restSecond)

set_option smartUnfolding false in
def pureSecondRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((pureSecond.sound stop count (.interchange returns) (inputs x y) .pure).run
          (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

/-- One effectful step on the first input. The exit has the response and the second input. -/
def emitOnly : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨Op.emit, emitArgs⟩ (.one
    (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there (.there .here)) .nil)⟩))

/-- The port map that exchanges the two inputs. -/
def swapInputs : PortMap [(), ()] [(), ()] := PortMap.exchange [()] [()] []

set_option smartUnfolding false in
/-- The computation of a diagram with a step and renamed ports is its computation at the
selected values. -/
def swappedRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        (((Diagram.renameRun stop count swapInputs emitOnly (inputs x y) .pure).subst
          (Impl.Agreement.refl lower)).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + y, Nat.lt_succ_self _⟩).val ≡ u + y := .refl

set_option smartUnfolding false in
/-- The identity law of renaming, for the computation. -/
def identityRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        (((Diagram.renameIdRun stop count emitOnly (inputs x y) .pure).subst
          (Impl.Agreement.refl lower)).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- The composition law of renaming, for the computation. -/
def twiceRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        (((Diagram.renameRenameRun stop count swapInputs swapInputs emitOnly (inputs x y)
            .pure).subst
          (Impl.Agreement.refl lower)).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + x, Nat.lt_succ_self _⟩).val ≡ u + x := .refl

set_option smartUnfolding false in
/-- After the substitution, the early order is one call of the store. -/
def earlyCall (x y : Nat) :
    (early.meaning stop count (inputs x y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (n + x) .nil)⟩ := .refl

set_option smartUnfolding false in
/-- The late order is the same call. -/
def lateCall (x y : Nat) :
    (late.meaning stop count (inputs x y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (n + x) .nil)⟩ := .refl

set_option smartUnfolding false in
def lateDirectCall (x y : Nat) :
    (lateDirect.meaning stop count (inputs x y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (n + x) .nil)⟩ := .refl

/-- The two diagrams of the derivation are one computation. -/
def sameComputation (x y : Nat) :
    (early.meaning stop count (inputs x y)).subst lower ≡
      (late.meaning stop count (inputs x y)).subst lower :=
  (earlyCall stop count x y).trans (lateCall stop count x y).symm

/-- The diagram with one exit is that computation too. -/
def sameDirect (x y : Nat) :
    (late.meaning stop count (inputs x y)).subst lower ≡
      (lateDirect.meaning stop count (inputs x y)).subst lower :=
  (lateCall stop count x y).trans (lateDirectCall stop count x y).symm

set_option smartUnfolding false in
def earlyRun (flag : Bool) (u v x y : Nat) :
    observe stop count early flag u v x y ≡ (x + y, u + x) := .refl

set_option smartUnfolding false in
def lateRun (flag : Bool) (u v x y : Nat) :
    observe stop count late flag u v x y ≡ (x + y, u + x) := .refl

/-- The two orders have the same static size. -/
def earlySize : early.size ≡ 2 := .refl

def lateSize : late.size ≡ 2 := .refl

/-! A pure step moves across two effectful steps. -/

abbrev Three : Exits Unit := [.one [(), (), ()]]

/-- The exit with the sum and the two responses. The context has the second response, the
first response, the sum, and the two inputs. -/
def doneThree : Diagram sig [(), (), (), (), ()] Three :=
  .exit ⟨_, .here, Boundary.only _,
    .cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))⟩

/-- After the sum and the first effectful step: the second effectful step, on the second
input. -/
def afterSum : (ca : (sig.output Op.add).Case) → (cb : (sig.output Op.emit).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [(), ()])) Three
  | ⟨_, .here⟩, ⟨_, .here⟩ =>
      .step ⟨Op.emit, .cons (.there (.there (.there .here))) .nil⟩ (.one doneThree)

/-- The sum, and then the two effectful steps. -/
def sumFirst : Diagram sig [(), ()] Three :=
  .step ⟨Op.add, addArgs⟩ fun ca => .step ⟨Op.emit, emitArgs.weaken _⟩ fun cb => afterSum ca cb

/-- The operand of the second effectful step in the context with the first response. -/
def secondArgs : PortMap [(), (), ()] [()] := .cons (.there (.there .here)) .nil

/-- The exit after the first effectful step, the sum, and the second effectful step. -/
def afterBoth : (ca : (sig.output Op.add).Case) → (cb : (sig.output Op.emit).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [(), (), ()])) Three
  | ⟨_, .here⟩, ⟨_, .here⟩ =>
      .exit ⟨_, .here, Boundary.only _,
        .cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))⟩

/-- After the first effectful step: the second effectful step, and then the sum. -/
def sumLastRest : (cb : (sig.output Op.emit).Case) → Diagram sig (cb.1 ++ [(), ()]) Three
  | ⟨_, .here⟩ =>
      .step ⟨Op.emit, secondArgs⟩ fun cb' =>
        .step ⟨Op.add, (addArgs.weaken [()]).weaken _⟩ fun ca =>
          (afterBoth ca cb').rename (PortMap.exchange _ _ _)

/-- The two effectful steps, and then the sum. -/
def sumLast : Diagram sig [(), ()] Three := .step ⟨Op.emit, emitArgs⟩ sumLastRest

/-- The result of the first interchange agrees with the first diagram of the rule. -/
def secondSource : Diagram.Agreement
    (.step ⟨Op.add, addArgs.weaken [()]⟩ fun ca =>
      (afterSum ca ⟨_, .here⟩).rename (PortMap.exchange _ _ _))
    (.step (S := sig) ⟨Op.add, addArgs.weaken [()]⟩ fun ca =>
      .step ⟨Op.emit, secondArgs.weaken _⟩ fun cb' => afterBoth ca cb') :=
  .step _ fun
    | ⟨_, .here⟩ => .step _ fun
        | ⟨_, .here⟩ => .refl _

/-- The second interchange, after the first effectful step. -/
def secondInterchange : (cb : (sig.output Op.emit).Case) →
    Diagram.Derivation (.interchange sig)
      (.step ⟨Op.add, addArgs.weaken _⟩ fun ca =>
        (afterSum ca cb).rename (PortMap.exchange _ _ _))
      (sumLastRest cb)
  | ⟨_, .here⟩ => .trans (.agree secondSource)
      (.rule (.swap (S := sig) Op.add Op.emit (.inl .refl) (addArgs.weaken [()]) secondArgs
        afterBoth))

/-- Two interchanges: at the first step, and then after the first effectful step. -/
def across : Diagram.Derivation (.interchange sig) sumFirst sumLast :=
  .trans (.rule (.swap (S := sig) Op.add Op.emit (.inl .refl) addArgs emitArgs afterSum))
    (Diagram.Derivation.step (R := Rules.interchange sig) (Γ := [(), ()])
      (rest' := sumLastRest) ⟨Op.emit, emitArgs⟩ secondInterchange)

/-- The three values of the one exit case. -/
def threeValues : Exits.At Three Value → Nat × Nat × Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ =>
      (out.lookup .here, out.lookup (.there .here), out.lookup (.there (.there .here)))

set_option smartUnfolding false in
/-- After the substitution, the first order is the two calls of the store. -/
def sumFirstCall (stop : Free (sig.interface Value) (Exits.At Three Value)) (count : Nat)
    (x y : Nat) :
    (sumFirst.meaning stop count (inputs x y)).subst lower ≡
      .request .one fun (n : Nat) => .request .one fun (m : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (n + x) (.cons (m + y) .nil))⟩ :=
  .refl

set_option smartUnfolding false in
/-- The other order is the same two calls. -/
def sumLastCall (stop : Free (sig.interface Value) (Exits.At Three Value)) (count : Nat)
    (x y : Nat) :
    (sumLast.meaning stop count (inputs x y)).subst lower ≡
      .request .one fun (n : Nat) => .request .one fun (m : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (x + y) (.cons (n + x) (.cons (m + y) .nil))⟩ :=
  .refl

/-- The soundness of the two interchanges. -/
def acrossSound (stop : Free (sig.interface Value) (Exits.At Three Value)) (count : Nat)
    (x y : Nat) :
    Free.Agreement ((sumFirst.meaning stop count (inputs x y)).subst lower)
      ((sumLast.meaning stop count (inputs x y)).subst lower) :=
  across.sound stop count (.interchange returns) (inputs x y) .pure

set_option smartUnfolding false in
/-- The payload after the transport along the identity of the returned values that the
soundness of the two interchanges gives. The payload has the second response of the store. -/
def acrossPayload (stop : Free (sig.interface Value) (Exits.At Three Value)) (count : Nat)
    (flag : Bool) (u v x y : Nat) : Nat :=
  (Identity.transport (fun n => Fin (n + 1))
    (Identity.cong (fun out => (threeValues out).2.2)
      ((acrossSound stop count x y).run (f := provider flag u v) (fun _ => .refl)))
    ⟨u + y, Nat.lt_succ_self _⟩).val

/-- The two interchanges with closed inputs. Only the kernel reduces the payload. The checks
with arbitrary inputs of the first group have each construction of this derivation. -/
theorem acrossKernel :
    acrossPayload (.pure ⟨_, .here, Boundary.only _, .cons 0 (.cons 0 (.cons 0 .nil))⟩) 0
      true 3 4 5 6 = 9 := by
  decide +kernel

/-- The derivation in the other direction: the sum moves before the two effectful steps. -/
def acrossBack : Diagram.Derivation (.interchange sig) sumLast sumFirst := .symm across

/-! One continuation of two control paths. -/

/-- The test of the first input. Each case has a different sum, and the two paths exit to one
case of the boundary of the continuation, with the sum as its port. -/
def branches : Diagram sig [(), ()] [.one [()], .one [(), ()]] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there .here) .nil)⟩ (.one
        (.exit ⟨_, .here, ⟨_, .here⟩, .cons .here .nil⟩))
    | ⟨_, .there .here⟩ => .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ (.one
        (.exit ⟨_, .here, ⟨_, .here⟩, .cons .here .nil⟩))

/-- The continuation has the sum only. It has one effectful step. -/
def after : Continuation sig (.one [()]) [.one [(), ()]] :=
  .one (.step ⟨.emit, .cons .here .nil⟩ (.one
    (.exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩)))

/-- The shared form: the two paths have one continuation. -/
def shared : Diagram sig [(), ()] [.one [(), ()]] := .seq branches after

/-- The copied form: each path has the continuation. -/
def copied : Diagram sig [(), ()] [.one [(), ()]] := branches.atExits after

set_option smartUnfolding false in
def sharedZero (flag : Bool) (u v y : Nat) :
    observe stop count shared flag u v 0 y ≡ (y + y, u + (y + y)) := .refl

set_option smartUnfolding false in
def sharedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count shared flag u v (x + 1) y ≡ (x + 1 + y, u + (x + 1 + y)) := .refl

set_option smartUnfolding false in
def copiedZero (flag : Bool) (u v y : Nat) :
    observe stop count copied flag u v 0 y ≡ (y + y, u + (y + y)) := .refl

set_option smartUnfolding false in
def copiedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count copied flag u v (x + 1) y ≡ (x + 1 + y, u + (x + 1 + y)) := .refl

/-- The agreement of the two forms, after the substitution. -/
def agreement (x y : Nat) :
    Free.Agreement ((shared.meaning stop count (inputs x y)).subst lower)
      ((copied.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.seqAtExits stop count branches after (inputs x y) .pure).subst
    (Impl.Agreement.refl lower)

set_option smartUnfolding false in
/-- The identity of the two returned values, from the agreement, is consumed through a
dependent payload in each case of the test. -/
def agreementZero (flag : Bool) (u v y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((agreement stop count 0 y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨y + y, Nat.lt_succ_self _⟩).val ≡ y + y := .refl

set_option smartUnfolding false in
def agreementSucc (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((agreement stop count (x + 1) y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + 1 + y, Nat.lt_succ_self _⟩).val ≡ x + 1 + y := .refl

/-- The shared form has one effectful step, and the copied form has two. -/
def sharedSize : shared.size ≡ 4 := .refl

def copiedSize : copied.size ≡ 5 := .refl

/-! A composite in a composite. -/

/-- The exits of the inner composite: the boundary of the outer continuation, and the
boundary of the outer composite. -/
abbrev Outer : Exits Unit := [.one [(), ()], .one [(), ()]]

/-- The test of the first input. The first path has a sum, and it exits to the inner
continuation. The second path exits past the inner continuation, to the outer continuation,
with the two inputs. -/
def innerFirst : Diagram sig [(), ()] (.one [()] :: Outer) :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there .here) .nil)⟩ (.one
        (.exit ⟨_, .here, ⟨_, .here⟩, .cons .here .nil⟩))
    | ⟨_, .there .here⟩ =>
        .exit ⟨_, .there .here, ⟨_, .here⟩, .cons .here (.cons (.there .here) .nil)⟩

/-- The inner continuation: one effectful step on the sum. It exits to the outer continuation
with the response and the sum. -/
def innerNext : Continuation sig (.one [()]) Outer :=
  .one (.step ⟨.emit, .cons .here .nil⟩ (.one
    (.exit ⟨_, .here, ⟨_, .here⟩, .cons .here (.cons (.there .here) .nil)⟩)))

/-- The outer continuation: the sum of its two ports. The exit has the sum and the first
port. -/
def outerNext : Continuation sig (.one [(), ()]) [.one [(), ()]] :=
  .one (.step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ (.one
    (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩)))

/-- The inner composite. -/
def inner : Diagram sig [(), ()] Outer := .seq innerFirst innerNext

/-- The shared form: the two paths of the inner composite have one outer continuation. -/
def nested : Diagram sig [(), ()] [.one [(), ()]] := .seq inner outerNext

/-- The copied form: the outer continuation at each exit of the inner composite. -/
def nestedCopied : Diagram sig [(), ()] [.one [(), ()]] := inner.atExits outerNext

set_option smartUnfolding false in
def nestedZero (flag : Bool) (u v y : Nat) :
    observe stop count nested flag u v 0 y ≡ (u + (y + y) + (y + y), u + (y + y)) := .refl

set_option smartUnfolding false in
def nestedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count nested flag u v (x + 1) y ≡ (x + 1 + y, x + 1) := .refl

set_option smartUnfolding false in
def nestedCopiedZero (flag : Bool) (u v y : Nat) :
    observe stop count nestedCopied flag u v 0 y ≡ (u + (y + y) + (y + y), u + (y + y)) := .refl

set_option smartUnfolding false in
def nestedCopiedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count nestedCopied flag u v (x + 1) y ≡ (x + 1 + y, x + 1) := .refl

/-- The agreement of the two forms, after the substitution. The copied form has the action of
a boundary map on the exits of the outer continuation, under the boundary of the inner
continuation. -/
def nestedAgreement (x y : Nat) :
    Free.Agreement ((nested.meaning stop count (inputs x y)).subst lower)
      ((nestedCopied.meaning stop count (inputs x y)).subst lower) :=
  (Diagram.seqAtExits stop count inner outerNext (inputs x y) .pure).subst
    (Impl.Agreement.refl lower)

set_option smartUnfolding false in
/-- The identity of the two returned values, from the agreement, is consumed through a
dependent payload in each case of the test. -/
def nestedAgreementZero (flag : Bool) (u v y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((nestedAgreement stop count 0 y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨u + (y + y), Nat.lt_succ_self _⟩).val ≡ u + (y + y) := .refl

set_option smartUnfolding false in
def nestedAgreementSucc (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).1)
        ((nestedAgreement stop count (x + 1) y).run (f := provider flag u v) (fun _ => .refl)))
      ⟨x + 1 + y, Nat.lt_succ_self _⟩).val ≡ x + 1 + y := .refl

/-- The shared form has one copy of the outer continuation, and the copied form has two. -/
def nestedSize : nested.size ≡ 4 := .refl

def nestedCopiedSize : nestedCopied.size ≡ 5 := .refl

/-! One step of two control paths with different continuations. -/

/-- The two cases of the test, with the two inputs as ports. -/
def paths : Boundary Unit := [[(), ()], [(), ()]]

/-- The bypass: a case for each path, with one port. -/
def bypass : Boundary Unit := [[()], [()]]

/-- The test. Each case exits to its own case of the entry of the frame, with the two
inputs. -/
def tested : Diagram sig [(), ()] [paths, .one [(), ()]] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .exit ⟨_, .here, ⟨_, .here⟩, .cons .here (.cons (.there .here) .nil)⟩
    | ⟨_, .there .here⟩ =>
        .exit ⟨_, .here, ⟨_, .there .here⟩, .cons .here (.cons (.there .here) .nil)⟩

/-- The shared diagram: one effectful step on its one port. -/
def call : Diagram sig [()] [.one [()]] :=
  .step ⟨.emit, .cons .here .nil⟩ (.one (.exit ⟨_, .here, Boundary.only _, .cons .here .nil⟩))

/-- The case of the bypass for each path, with the second input as its port. -/
def keep : (c : paths.Case) → bypass.At (Port c.1)
  | ⟨_, .here⟩ => ⟨⟨_, .here⟩, .cons (.there .here) .nil⟩
  | ⟨_, .there .here⟩ => ⟨⟨_, .there .here⟩, .cons (.there .here) .nil⟩

/-- The port of the shared step for each path: the first input. -/
def enter : (c : paths.Case) → PortMap c.1 [()]
  | ⟨_, .here⟩ => .cons .here .nil
  | ⟨_, .there .here⟩ => .cons .here .nil

/-- After the shared step, the first path adds the response and the kept input, and the second
path doubles the kept input. The exit has the sum and the response. -/
def afterCall : (c : (bypass.product (.one [()])).Case) → Diagram sig c.1 [.one [(), ()]]
  | ⟨_, .here⟩ => .step ⟨.add, .cons .here (.cons (.there .here) .nil)⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))
  | ⟨_, .there .here⟩ => .step ⟨.add, .cons (.there .here) (.cons (.there .here) .nil)⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))

/-- One copy of the effectful step for the two paths. The bypass keeps the path and the second
input, and the step has the first input. -/
def framed : Diagram sig [(), ()] [.one [(), ()]] :=
  .seq tested (.frame (M := bypass) keep enter call (.copair afterCall))

/-- A copy of the effectful step in each path. -/
def stepCopied : Diagram sig [(), ()] [.one [(), ()]] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .step ⟨.emit, .cons .here .nil⟩ (.one
        (.step ⟨.add, .cons .here (.cons (.there (.there .here)) .nil)⟩ (.one
          (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))))
    | ⟨_, .there .here⟩ => .step ⟨.emit, .cons .here .nil⟩ (.one
        (.step ⟨.add, .cons (.there (.there .here)) (.cons (.there (.there .here)) .nil)⟩ (.one
          (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))))

/-- A derivation in a frame, by the congruence of a frame. The continuation has the
agreement, the symmetry, the transitivity, and the congruence of a copairing. -/
def inFrame : Diagram.Derivation (.interchange sig) framed framed :=
  .seq (.agree (.refl tested))
    (.frame keep enter (.agree (.refl call))
      (.trans (.agree (.refl (.copair afterCall)))
        (.symm (.copair fun _ => .agree (.refl _)))))

set_option smartUnfolding false in
def inFrameRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((inFrame.sound stop count (.interchange returns) (inputs (x + 1) y) .pure).run
          (f := provider flag u v) (fun _ => .refl)))
      ⟨u + (x + 1), Nat.lt_succ_self _⟩).val ≡ u + (x + 1) := .refl

set_option smartUnfolding false in
def framedZero (flag : Bool) (u v y : Nat) :
    observe stop count framed flag u v 0 y ≡ (u + 0 + y, u + 0) := .refl

set_option smartUnfolding false in
def framedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count framed flag u v (x + 1) y ≡ (y + y, u + (x + 1)) := .refl

set_option smartUnfolding false in
def stepCopiedZero (flag : Bool) (u v y : Nat) :
    observe stop count stepCopied flag u v 0 y ≡ (u + 0 + y, u + 0) := .refl

set_option smartUnfolding false in
def stepCopiedSucc (flag : Bool) (u v x y : Nat) :
    observe stop count stepCopied flag u v (x + 1) y ≡ (y + y, u + (x + 1)) := .refl

set_option smartUnfolding false in
/-- After the substitution, the frame is one call of the store, in each case of the test. -/
def framedCallZero (y : Nat) :
    (framed.meaning stop count (inputs 0 y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (n + 0 + y) (.cons (n + 0) .nil)⟩ := .refl

set_option smartUnfolding false in
def framedCallSucc (x y : Nat) :
    (framed.meaning stop count (inputs (x + 1) y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (y + y) (.cons (n + (x + 1)) .nil)⟩ := .refl

set_option smartUnfolding false in
def stepCopiedCallZero (y : Nat) :
    (stepCopied.meaning stop count (inputs 0 y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (n + 0 + y) (.cons (n + 0) .nil)⟩ := .refl

set_option smartUnfolding false in
def stepCopiedCallSucc (x y : Nat) :
    (stepCopied.meaning stop count (inputs (x + 1) y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (y + y) (.cons (n + (x + 1)) .nil)⟩ := .refl

/-- The frame and the copies are one computation, in each case of the test. -/
def frameZero (y : Nat) :
    (framed.meaning stop count (inputs 0 y)).subst lower ≡
      (stepCopied.meaning stop count (inputs 0 y)).subst lower :=
  (framedCallZero stop count y).trans (stepCopiedCallZero stop count y).symm

def frameSucc (x y : Nat) :
    (framed.meaning stop count (inputs (x + 1) y)).subst lower ≡
      (stepCopied.meaning stop count (inputs (x + 1) y)).subst lower :=
  (framedCallSucc stop count x y).trans (stepCopiedCallSucc stop count x y).symm

/-- The frame has one effectful step, and the copied form has two. -/
def framedSize : framed.size ≡ 4 := .refl

def stepCopiedSize : stepCopied.size ≡ 5 := .refl

/-! One step of two of three control paths. -/

/-- Two tests. The first path and the third path exit to their cases of the entry of the
frame, with the two inputs. The second path has a sum, and it exits past the frame with the
sum and the second input. -/
def threePaths : Diagram sig [(), ()] [paths, .one [(), ()]] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .exit ⟨_, .here, ⟨_, .here⟩, .cons .here (.cons (.there .here) .nil)⟩
    | ⟨_, .there .here⟩ => .step ⟨.isZero, .cons (.there .here) .nil⟩ fun
        | ⟨_, .here⟩ => .step ⟨.add, .cons .here (.cons .here .nil)⟩ (.one
            (.exit ⟨_, .there .here, ⟨_, .here⟩,
              .cons .here (.cons (.there (.there .here)) .nil)⟩))
        | ⟨_, .there .here⟩ =>
            .exit ⟨_, .here, ⟨_, .there .here⟩, .cons .here (.cons (.there .here) .nil)⟩

/-- One copy of the effectful step for the first path and the third path. The second path
does not have the step. -/
def partFramed : Diagram sig [(), ()] [.one [(), ()]] :=
  .seq threePaths (.frame (M := bypass) keep enter call (.copair afterCall))

set_option smartUnfolding false in
def partFramedFirst (flag : Bool) (u v y : Nat) :
    observe stop count partFramed flag u v 0 y ≡ (u + 0 + y, u + 0) := .refl

set_option smartUnfolding false in
def partFramedSecond (flag : Bool) (u v x : Nat) :
    observe stop count partFramed flag u v (x + 1) 0 ≡ (x + 1 + (x + 1), 0) := .refl

set_option smartUnfolding false in
def partFramedThird (flag : Bool) (u v x y : Nat) :
    observe stop count partFramed flag u v (x + 1) (y + 1) ≡ (y + 1 + (y + 1), u + (x + 1)) := .refl

set_option smartUnfolding false in
/-- After the substitution, the first path is one call of the store. -/
def partFramedCallFirst (y : Nat) :
    (partFramed.meaning stop count (inputs 0 y)).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (n + 0 + y) (.cons (n + 0) .nil)⟩ := .refl

set_option smartUnfolding false in
/-- The second path has no call of the store. -/
def partFramedCallSecond (x : Nat) :
    (partFramed.meaning stop count (inputs (x + 1) 0)).subst lower ≡
      .pure ⟨_, .here, Boundary.only _, .cons (x + 1 + (x + 1)) (.cons 0 .nil)⟩ := .refl

set_option smartUnfolding false in
/-- The third path is one call of the store. -/
def partFramedCallThird (x y : Nat) :
    (partFramed.meaning stop count (inputs (x + 1) (y + 1))).subst lower ≡
      .request .one fun (n : Nat) =>
        .pure ⟨_, .here, Boundary.only _, .cons (y + 1 + (y + 1)) (.cons (n + (x + 1)) .nil)⟩ :=
  .refl

/-- The diagram has one effectful step for the two paths of the frame. -/
def partFramedSize : partFramed.size ≡ 6 := .refl

/-- The exit with the two inputs. -/
def bothInputs : Exits.At [.one [(), ()]] (Port [(), ()]) :=
  ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩

/-- An exit past the frame, and then the frame. -/
def pastExit : Diagram sig [(), ()] [.one [(), ()]] :=
  .seq (.exit (bothInputs.there paths)) (.frame (M := bypass) keep enter call (.copair afterCall))

/-- The second exit equation of the control sum: the exit goes past the frame. -/
def pastDerivation : Diagram.Derivation (.control sig) pastExit (.exit bothInputs) :=
  .rule (Sum.inr (Sum.inr (.exit bothInputs _)))

set_option smartUnfolding false in
/-- The identity of the two returned values, from the soundness of the rule, is consumed
through a dependent payload. -/
def pastSoundRun (flag : Bool) (u v x y : Nat) :
    (Identity.transport (fun n => Fin (n + 1))
      (Identity.cong (fun out => (values out).2)
        ((pastDerivation.sound stop count (.control returns) (inputs x y) .pure).run
          (f := provider flag u v) (fun _ => .refl)))
      ⟨y, Nat.lt_succ_self _⟩).val ≡ y := .refl

-- Compiled observations supplement the kernel checks above.
#guard observe limit 0 early true 3 4 5 6 == (11, 8)
#guard observe limit 0 late true 3 4 5 6 == (11, 8)
#guard observe limit 0 lateDirect true 3 4 5 6 == (11, 8)
#guard observe limit 0 shared true 3 4 0 6 == (12, 15)
#guard observe limit 0 copied true 3 4 5 6 == (11, 14)
#guard observe limit 0 framed true 3 4 0 6 == (9, 3)
#guard observe limit 0 framed true 3 4 5 6 == (12, 8)
#guard observe limit 0 stepCopied true 3 4 5 6 == (12, 8)
#guard observe limit 0 nested true 3 4 0 6 == (27, 15)
#guard observe limit 0 nestedCopied true 3 4 5 6 == (11, 5)
#guard observe limit 0 partFramed true 3 4 0 6 == (9, 3)
#guard observe limit 0 partFramed true 3 4 5 0 == (10, 0)
#guard observe limit 0 partFramed true 3 4 5 6 == (12, 8)
#guard shared.size == 4 && copied.size == 5 && framed.size == 4 && stepCopied.size == 5
#guard nested.size == 4 && nestedCopied.size == 5 && partFramed.size == 6

end Draft.Checks.Diagram

/-- info: 'Draft.Checks.Diagram.interchangeRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.interchangeRun

/-- info: 'Draft.Checks.Diagram.exitSoundRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.exitSoundRun

/-- info: 'Draft.Checks.Diagram.compositeRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.compositeRun

/-- info: 'Draft.Checks.Diagram.acrossPayload' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.acrossPayload

/-- info: 'Draft.Checks.Diagram.agreementSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.agreementSucc

/-- info: 'Draft.Checks.Diagram.nestedAgreementSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.nestedAgreementSucc

/-- info: 'Draft.Checks.Diagram.frameSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.frameSucc

/-- info: 'Draft.Checks.Diagram.partFramedCallThird' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Diagram.partFramedCallThird
