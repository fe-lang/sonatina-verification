import Draft.Checks.Lift
import Draft.Checks.State

/-! Two alternatives that share one effectful step, on a machine with an invariant of the
runtime.

The signature has a read, a write, and a pure test for zero. The runtime of the machine has the
value of the cell and the number of the reads.

The diagram tests its first input. The two alternatives share one read of the cell, in a frame.
The bypass of the frame keeps the alternative and the second input. After the read, the first
alternative writes the kept input, and the second alternative reads the cell again. The two
alternatives exit to one case, with two values.

The first group has the runs on the machine of the lowering, for an arbitrary second input and
an arbitrary runtime. Each run has the steps of its alternative only: the first has one read
and the kept input in the cell, and the second has two reads and the first value of the cell.

The second group has the frame equation. It relates the frame to the copairing that has the
frame of each alternative alone. The two diagrams have one run on the machine, and a check
consumes the identity of the two runs through a dependent payload.

The third group has the invariant of the runtime: a lower bound of the number of the reads,
with the difference. The specification of each call has the invariant before the call and
after it, and the machine of the cell has evidence of it. The specification of the test has
the fact of its case. The lift of the diagram is built by its constructors. The shared read
takes the invariant from the entry of the frame, and the continuation of each alternative
receives the invariant at the runtime after the read. The exit has the invariant at the last
runtime. On the first alternative, it has the identity of the second value with the kept
input, from the fact of the test.

The run on the machine gives the evidence at the result. Two witnesses of one runtime give
different payloads, and the payload has the number of the reads of the alternative. The frame
equation moves the verified implementation to the form with the frame of each alternative
alone, with the same payloads. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.Branch

open Container
open Draft.Checks.Lift (ZeroCase)
open Draft.Checks.State (Cell cellMachine Value Two values reads)

inductive Op where
  | get
  | put
  | isZero

/-- One value type. `get` and `put` are effectful. `isZero` is a pure test: its output boundary
has two cases with no port. -/
def sig : Signature Unit where
  Op := Op
  kind
    | .get => .effectful
    | .put => .effectful
    | .isZero => .pure
  input
    | .get => []
    | .put => [()]
    | .isZero => [()]
  output
    | .get => .one [()]
    | .put => .one []
    | .isZero => [[], []]

/-- The lowering. A read and a write are one call each. The test returns without a call, and
its first case is the case of zero. -/
def lower : Impl (sig.interface Value) (cell Nat)
  | ⟨.get, _⟩ => .request .get fun (value : Nat) => .pure ⟨Boundary.only _, .cons value .nil⟩
  | ⟨.put, args⟩ => .request (.put (args.lookup .here)) fun _ => .pure ⟨Boundary.only _, .nil⟩
  | ⟨.isZero, args⟩ =>
      match args.lookup .here with
      | 0 => .pure ⟨⟨_, .here⟩, .nil⟩
      | _ + 1 => .pure ⟨⟨_, .there .here⟩, .nil⟩

/-- The test returns without a call. -/
def returns : ImplDep (sig.pureSpec Value) (DepPoly.noCall.{0, 0, 0, 0} (cell Nat)) lower
  | ⟨.isZero, .cons 0 .nil⟩, _ => .pure ⟨⟩
  | ⟨.isZero, .cons (_ + 1) .nil⟩, _ => .pure ⟨⟩

/-! The diagram. -/

/-- The two cases of the test, with the two inputs as ports. -/
def paths : Boundary Unit := [[(), ()], [(), ()]]

/-- The bypass: a case for each alternative, with one port. -/
def bypass : Boundary Unit := [[()], [()]]

/-- The test. Each case exits to its own case of the entry of the frame, with the two
inputs. -/
def tested : Diagram sig [(), ()] [paths, .one [(), ()]] :=
  .step ⟨.isZero, .cons .here .nil⟩ fun
    | ⟨_, .here⟩ => .exit ⟨_, .here, ⟨_, .here⟩, .cons .here (.cons (.there .here) .nil)⟩
    | ⟨_, .there .here⟩ =>
        .exit ⟨_, .here, ⟨_, .there .here⟩, .cons .here (.cons (.there .here) .nil)⟩

/-- The shared diagram: one read of the cell. -/
def read : Diagram sig [] [.one [()]] :=
  .step ⟨.get, .nil⟩ (.one (.exit ⟨_, .here, Boundary.only _, .cons .here .nil⟩))

/-- The case of the bypass for each alternative, with the second input as its port. -/
def keep : (c : paths.Case) → bypass.At (Port c.1)
  | ⟨_, .here⟩ => ⟨⟨_, .here⟩, .cons (.there .here) .nil⟩
  | ⟨_, .there .here⟩ => ⟨⟨_, .there .here⟩, .cons (.there .here) .nil⟩

/-- The shared read has no operand. -/
def enter : (c : paths.Case) → PortMap c.1 [] := fun _ => .nil

/-- After the shared read, the first alternative writes the kept input, and its exit has the
value of the read and the kept input. The second alternative reads the cell again, and its exit
has the two values. -/
def afterRead : (c : (bypass.product (.one [()])).Case) → Diagram sig c.1 Two
  | ⟨_, .here⟩ => .step ⟨.put, .cons (.there .here) .nil⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons .here (.cons (.there .here) .nil)⟩))
  | ⟨_, .there .here⟩ => .step ⟨.get, .nil⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩))

/-- One copy of the read for the two alternatives. The bypass keeps the alternative and the
second input. -/
def framed : Diagram sig [(), ()] Two :=
  .seq tested (.frame (M := bypass) keep enter read (.copair afterRead))

/-- The copairing that has the frame of each alternative alone. Each alternative has a copy of
the read. -/
def framedEach : Diagram sig [(), ()] Two :=
  .seq tested (.copair (Continuation.frameAt keep enter read (.copair afterRead)))

/-- The frame equation of the control sum relates the two forms, by the congruence of a
composite. -/
def unshare : Diagram.Derivation (.control sig) framed framedEach :=
  .seq (.agree (.refl tested)) (.rule (Sum.inl (.frame keep enter read (.copair afterRead))))

/-! The runs on the machine of the lowering. -/

/-- The run of a diagram on the machine of the lowering, with the two values. -/
def observed (d : Diagram sig [(), ()] Two) (n : Nat)
    (stop : Free (sig.interface Value) (Nat × Nat)) (x y : Nat) (s : Cell) :
    Empty ⊕ ((Nat × Nat) × Cell) :=
  (cellMachine.impl lower).run (d.run stop n (.cons x (.cons y .nil)) fun r => .pure (values r)) s

set_option smartUnfolding false in
/-- The first alternative has one read, and the cell has the kept input. -/
def framedZero (n y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed framed n stop 0 y (c, k) ≡ .inr ((c, y), (y, k + 1)) := .refl

set_option smartUnfolding false in
/-- The second alternative has two reads, and the cell has its first value. -/
def framedSucc (n x y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed framed n stop (x + 1) y (c, k) ≡ .inr ((c, c), (c, k + 2)) := .refl

set_option smartUnfolding false in
def eachZero (n y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed framedEach n stop 0 y (c, k) ≡ .inr ((c, y), (y, k + 1)) := .refl

set_option smartUnfolding false in
def eachSucc (n x y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed framedEach n stop (x + 1) y (c, k) ≡ .inr ((c, c), (c, k + 2)) := .refl

/-! The frame equation on the machine. -/

/-- The two forms have one run on the machine of the lowering: the soundness of the
derivation. -/
def sameRun (n x y : Nat) (s : Cell) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed framed n stop x y s ≡ observed framedEach n stop x y s :=
  unshare.sound stop n ((Rules.Sound.control returns).machine cellMachine)
    (.cons x (.cons y .nil)) (fun r => .pure (values r)) s

set_option smartUnfolding false in
/-- The identity of the two runs is consumed through a dependent payload, for an arbitrary
second input and an arbitrary runtime, in each alternative. -/
def unshareZero (n y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    (Identity.transport (fun out => Fin (reads out + 1)) (sameRun n 0 y (c, k) stop)
      ⟨k + 1, Nat.lt_succ_self _⟩).val ≡ k + 1 := .refl

set_option smartUnfolding false in
def unshareSucc (n x y c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    (Identity.transport (fun out => Fin (reads out + 1)) (sameRun n (x + 1) y (c, k) stop)
      ⟨k + 2, Nat.lt_succ_self _⟩).val ≡ k + 2 := .refl

set_option smartUnfolding false in
/-- The frame has one copy of the read, and the other form has a copy in each alternative. -/
def sizes : (framed.size, framedEach.size) ≡ (4, 7) := .refl

/-! The invariant of the runtime. -/

/-- The invariant of the runtime: a lower bound of the number of the reads, with the
difference. -/
abbrev Reads (s : Cell) : Type := (b : Nat) × ((j : Nat) × (s.2 ≡ b + j))

/-- A stop has no evidence. -/
abbrev Stops : Empty → Type := fun _ => Empty

/-- The specification of the calls of the cell, with no runtime. -/
def cellSpec : DepPoly.{0, 0, 0, 0} (cell Nat) where
  Pre _ := Unit
  Post _ _ _ := Unit

/-- The machine of the cell keeps the invariant. A read has one more in the difference, and a
write keeps the witness. -/
def keeps : Evidence (cellSpec.invariant Reads Stops) cellMachine
  | (.get, _), (inv, _) => ((), ⟨inv.1, inv.2.1 + 1, Identity.cong (fun k => k + 1) inv.2.2⟩)
  | (.put _, _), (inv, _) => ((), inv)

/-- The specification of each operation, with no runtime. The test has the fact of its case. -/
def opSpec : DepPoly.{0, 0, 0, 0} (sig.interface Value) where
  Pre _ := Unit
  Post
    | ⟨.get, _⟩, _, _ => Unit
    | ⟨.put, _⟩, _, _ => Unit
    | ⟨.isZero, args⟩, _, resp => ZeroCase (args.lookup .here) resp.1

/-- The lowering is a verified implementation. -/
def lowerDep : ImplDep opSpec cellSpec lower
  | ⟨.get, _⟩, _ => .request () fun _ _ => .pure ()
  | ⟨.put, _⟩, _ => .request () fun _ _ => .pure ()
  | ⟨.isZero, .cons 0 .nil⟩, _ => .pure (Identity.refl : (0 : Nat) ≡ 0)
  | ⟨.isZero, .cons (k + 1) .nil⟩, _ => .pure (⟨k, .refl⟩ : (j : Nat) × (k + 1 ≡ j + 1))

/-- The condition of the two values at the exit, for the two inputs. At a first input of zero,
the second value is the second input. -/
def Kept : Nat → Nat → Nat × Nat → Type
  | 0, y, v => v.2 ≡ y
  | _ + 1, _, _ => Unit

/-- The specification of the diagram, with no runtime. -/
def wholeSpec : DepPoly.{0, 0, 0, 0} (Diagram.interface Value [(), ()] Two) where
  Pre _ := Unit
  Post env _ out := Kept (env.lookup .here) (env.lookup (.there .here)) (values out)

/-- The specification of the calls with a runtime: the invariant before a call and after it. -/
abbrev callSpec : DepPoly.{0, 0, 0, 0} ((sig.interface Value).runtime Cell Empty) :=
  opSpec.invariant Reads Stops

/-- The specification of the calls of the cell with a runtime. -/
abbrev cellInvariant : DepPoly.{0, 0, 0, 0} ((cell Nat).runtime Cell Empty) :=
  cellSpec.invariant Reads Stops

/-- The specification of the diagram with a runtime: the invariant at the first runtime and at
the last runtime. -/
abbrev framedSpec :
    DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [(), ()] Two).runtime Cell Empty) :=
  wholeSpec.invariant Reads Stops

/-- The condition at the entry of the frame, for the two inputs: the fact of the test, and on
the first alternative the identity of the second port with the second input. -/
def Entered (x y : Nat) : paths.At Value → Type
  | ⟨⟨_, .here⟩, vals⟩ => (x ≡ 0) × (vals.lookup (.there .here) ≡ y)
  | ⟨⟨_, .there .here⟩, _⟩ => (m : Nat) × (x ≡ m + 1)

set_option smartUnfolding false in
/-- The lift of the framed form, by the constructors of the diagram. The test establishes the
condition at the entry of the frame. The shared read takes the invariant from that entry, and
the continuation of each alternative receives the invariant at the runtime after the read. The
exit has the invariant at the last runtime. -/
def framedLift (n : Nat) : framed.StateLift callSpec n framedSpec (fun _ _ _ => Empty) :=
  fun env _ pre =>
    Diagram.StateDep.seq (S := sig)
      (fun a s => Entered (env.lookup .here) (env.lookup (.there .here)) a × Reads s) tested
      (.frame (M := bypass) keep enter read (.copair afterRead))
      (Diagram.StateDep.step (S := sig) ⟨Op.isZero, .cons .here .nil⟩ _ (pre.1, ())
        (fun e _ => e.elim)
        fun
          | ⟨⟨_, .here⟩, .nil⟩, _, post => Diagram.StateDep.exit _ ((post.1, .refl), post.2)
          | ⟨⟨_, .there .here⟩, .nil⟩, _, post => Diagram.StateDep.exit _ (post.1, post.2))
      fun
        | ⟨⟨_, .here⟩, .cons _ (.cons kept .nil)⟩, _, entered =>
            Continuation.StateDep.frame (S := sig) (M := bypass) (fun _ s => Reads s) keep enter
              read (.copair afterRead)
              (Diagram.StateDep.step (S := sig) ⟨Op.get, .nil⟩ _ (entered.2, ())
                (fun e _ => e.elim)
                fun
                  | ⟨⟨_, .here⟩, .cons _ .nil⟩, _, post => Diagram.StateDep.exit _ post.2)
              fun
                | ⟨⟨_, .here⟩, .cons first .nil⟩, _, inv =>
                    Continuation.StateDep.copair _
                      (Diagram.StateDep.step (S := sig) ⟨Op.put, .cons (.there .here) .nil⟩ _
                        (inv, ()) (fun e _ => e.elim)
                        fun
                          | ⟨⟨_, .here⟩, .nil⟩, _, post =>
                              Diagram.StateDep.exit _
                                (Identity.transport
                                  (fun x => Kept x (env.lookup (.there .here)) (first, kept))
                                  entered.1.1.symm entered.1.2, post.2))
        | ⟨⟨_, .there .here⟩, .cons _ (.cons _ .nil)⟩, _, entered =>
            Continuation.StateDep.frame (S := sig) (M := bypass) (fun _ s => Reads s) keep enter
              read (.copair afterRead)
              (Diagram.StateDep.step (S := sig) ⟨Op.get, .nil⟩ _ (entered.2, ())
                (fun e _ => e.elim)
                fun
                  | ⟨⟨_, .here⟩, .cons _ .nil⟩, _, post => Diagram.StateDep.exit _ post.2)
              fun
                | ⟨⟨_, .here⟩, .cons first .nil⟩, _, inv =>
                    Continuation.StateDep.copair _
                      (Diagram.StateDep.step (S := sig) ⟨Op.get, .nil⟩ _ (inv, ())
                        (fun e _ => e.elim)
                        fun
                          | ⟨⟨_, .here⟩, .cons second .nil⟩, _, post =>
                              Diagram.StateDep.exit _
                                (Identity.transport
                                  (fun x => Kept x (env.lookup (.there .here)) (first, second))
                                  entered.1.2.symm (), post.2))

variable (stop : Free (sig.interface Value) (Exits.At Two Value)) (count : Nat)

/-- The verified diagram with a runtime, and then the verified lowering with a runtime: a
verified implementation by the calls of the cell, for the invariant. -/
def framedLowered :
    ImplDep framedSpec cellInvariant ((framed.impl stop count).thread.trans lower.thread) :=
  ((framedLift count).impl fun _ _ _ _ e => e.elim).trans lowerDep.thread

/-- The frame equation as a map of verified implementations with a runtime: the verified form
with the frame of each alternative alone. -/
def eachLowered :
    ImplDep framedSpec cellInvariant ((framedEach.impl stop count).thread.trans lower.thread) :=
  unshare.stateLift (.control returns) stop count (framedLowered stop count)

/-- The evidence at the result of the run on the machine of the cell, which keeps the
invariant. -/
def evidence {f : Impl ((Diagram.interface Value [(), ()] Two).runtime Cell Empty)
      ((cell Nat).runtime Cell Empty)}
    (ff : ImplDep framedSpec cellInvariant f) (x y : Nat) (s : Cell) (inv : Reads s) :
    framedSpec.Post (.cons x (.cons y .nil), s) (inv, ())
      (f.run cellMachine (.cons x (.cons y .nil), s)) :=
  ff.run keeps (.cons x (.cons y .nil), s) (inv, ())

/-- The difference in the invariant at a result. -/
def difference {a : All Value [(), ()] × Cell} {pre : framedSpec.Pre a} :
    {out : Empty ⊕ (Exits.At Two Value × Cell)} → framedSpec.Post a pre out → Nat
  | .inr _, post => post.2.2.1

/-- The number of the reads at a result, through the identity in the invariant. -/
def counter {a : All Value [(), ()] × Cell} {pre : framedSpec.Pre a} :
    {out : Empty ⊕ (Exits.At Two Value × Cell)} → framedSpec.Post a pre out → Nat
  | .inr out, post =>
      (Identity.transport (fun k => Fin (k + 1)) post.2.2.2 ⟨out.2.2, Nat.lt_succ_self _⟩).val

/-- The second value at a result of the first alternative, through the identity with the kept
input. -/
def keptValue {y : Nat} {s : Cell} {pre : framedSpec.Pre (.cons 0 (.cons y .nil), s)} :
    {out : Empty ⊕ (Exits.At Two Value × Cell)} →
      framedSpec.Post (.cons 0 (.cons y .nil), s) pre out → Nat
  | .inr out, post =>
      (Identity.transport (fun k => Fin (k + 1)) post.1
        ⟨(values out.1).2, Nat.lt_succ_self _⟩).val

set_option smartUnfolding false in
/-- The first alternative has one read. Two witnesses of one runtime give different payloads,
for an arbitrary second input, an arbitrary cell, and an arbitrary bound. -/
def framedZeroWide (y c b j : Nat) :
    difference (evidence (framedLowered stop count) 0 y (c, b + j) ⟨b, j, .refl⟩) ≡ j + 1 :=
  .refl

set_option smartUnfolding false in
def framedZeroTight (y c b j : Nat) :
    difference (evidence (framedLowered stop count) 0 y (c, b + j) ⟨b + j, 0, .refl⟩) ≡ 1 :=
  .refl

set_option smartUnfolding false in
/-- The second alternative has two reads. -/
def framedSuccWide (x y c b j : Nat) :
    difference (evidence (framedLowered stop count) (x + 1) y (c, b + j) ⟨b, j, .refl⟩) ≡
      j + 2 := .refl

set_option smartUnfolding false in
def framedSuccTight (x y c b j : Nat) :
    difference (evidence (framedLowered stop count) (x + 1) y (c, b + j) ⟨b + j, 0, .refl⟩) ≡
      2 := .refl

set_option smartUnfolding false in
/-- The identity of the number of the reads at the last runtime is consumed through a
dependent payload. -/
def framedZeroCounter (y c b j : Nat) :
    counter (evidence (framedLowered stop count) 0 y (c, b + j) ⟨b, j, .refl⟩) ≡ b + j + 1 :=
  .refl

set_option smartUnfolding false in
def framedSuccCounter (x y c b j : Nat) :
    counter (evidence (framedLowered stop count) (x + 1) y (c, b + j) ⟨b, j, .refl⟩) ≡
      b + j + 2 := .refl

set_option smartUnfolding false in
/-- The kept input is the second value after the shared read. The identity goes through the
condition at the entry of the frame, and it is consumed through a dependent payload. -/
def framedZeroKept (y c b j : Nat) :
    keptValue (evidence (framedLowered stop count) 0 y (c, b + j) ⟨b, j, .refl⟩) ≡ y := .refl

set_option smartUnfolding false in
/-- After the frame equation, the evidence gives the same payloads. -/
def eachZeroWide (y c b j : Nat) :
    difference (evidence (eachLowered stop count) 0 y (c, b + j) ⟨b, j, .refl⟩) ≡ j + 1 :=
  .refl

set_option smartUnfolding false in
def eachZeroTight (y c b j : Nat) :
    difference (evidence (eachLowered stop count) 0 y (c, b + j) ⟨b + j, 0, .refl⟩) ≡ 1 :=
  .refl

set_option smartUnfolding false in
def eachSuccWide (x y c b j : Nat) :
    difference (evidence (eachLowered stop count) (x + 1) y (c, b + j) ⟨b, j, .refl⟩) ≡
      j + 2 := .refl

set_option smartUnfolding false in
def eachSuccCounter (x y c b j : Nat) :
    counter (evidence (eachLowered stop count) (x + 1) y (c, b + j) ⟨b, j, .refl⟩) ≡
      b + j + 2 := .refl

set_option smartUnfolding false in
def eachZeroKept (y c b j : Nat) :
    keptValue (evidence (eachLowered stop count) 0 y (c, b + j) ⟨b, j, .refl⟩) ≡ y := .refl

end Draft.Checks.Branch

/-- info: 'Draft.Checks.Branch.framedZero' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedZero

/-- info: 'Draft.Checks.Branch.framedSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedSucc

/-- info: 'Draft.Checks.Branch.eachZero' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachZero

/-- info: 'Draft.Checks.Branch.eachSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachSucc

/-- info: 'Draft.Checks.Branch.unshareZero' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.unshareZero

/-- info: 'Draft.Checks.Branch.unshareSucc' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.unshareSucc

/-- info: 'Draft.Checks.Branch.sizes' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.sizes

/-- info: 'Draft.Checks.Branch.framedZeroWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedZeroWide

/-- info: 'Draft.Checks.Branch.framedZeroTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedZeroTight

/-- info: 'Draft.Checks.Branch.framedSuccWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedSuccWide

/-- info: 'Draft.Checks.Branch.framedSuccTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedSuccTight

/-- info: 'Draft.Checks.Branch.framedZeroCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedZeroCounter

/-- info: 'Draft.Checks.Branch.framedSuccCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedSuccCounter

/-- info: 'Draft.Checks.Branch.framedZeroKept' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.framedZeroKept

/-- info: 'Draft.Checks.Branch.eachZeroWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachZeroWide

/-- info: 'Draft.Checks.Branch.eachZeroTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachZeroTight

/-- info: 'Draft.Checks.Branch.eachSuccWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachSuccWide

/-- info: 'Draft.Checks.Branch.eachSuccCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachSuccCounter

/-- info: 'Draft.Checks.Branch.eachZeroKept' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Branch.eachZeroKept
