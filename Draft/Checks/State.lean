import Draft.Runtime

/-! Diagrams that read and write one cell, on a machine.

The signature has a read, a write, and a pure successor. The runtime of the machine has the
value of the cell and the number of the reads.

The first diagram reads the cell, keeps the value, writes its successor, and reads the cell
again. The value that it keeps and the value of the second read are different, and the run has
two reads: the two uses of the first value do not read the cell again. The check has an
arbitrary cell.

The second group has a write and a read in the two orders. The two runs give different values,
so no rule exchanges two steps on the cell without a law of the cell.

The third group has the first diagram with a specification that relates two runtimes. The
specification of the calls is the graph of the machine, and the evidence of the diagram is
built by its constructors. The run on the machine gives the evidence at its result: the two
values, and the last runtime as a function of the first runtime.

The fourth group has a lowering to the interface of the cell: a read and a write are one call
each, and the successor returns without a call. The machine of the lowering is the machine of
the signature. The successor and a read have two orders, and the interchange derivation
relates them. The two diagrams have one run on the machine of the lowering, for an arbitrary
input and an arbitrary cell.

The specification of the two diagrams relates two runtimes, and a witness of its precondition
has a lower bound of the number of the reads. The lift of the first order is built by its
constructors. Its composition with the lowering is a verified implementation by the calls of
the cell, and the interchange derivation moves it to the second order. The run on the machine
of the cell gives the evidence at the result, and two witnesses of one runtime give different
payloads.

The fifth group has the evidence of the machine of a diagram. The interchange rule holds on the
machine of the lowering. The run of the verified first order on that machine is the evidence of
its machine, and the derivation moves it to the machine of the second order, with the same
payloads. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude

namespace Draft.Checks.State

open Container

inductive Op where
  | get
  | put
  | succ

/-- One value type. `get` and `put` are effectful. `succ` is pure. -/
def sig : Signature Unit where
  Op := Op
  kind
    | .get => .effectful
    | .put => .effectful
    | .succ => .pure
  input
    | .get => []
    | .put => [()]
    | .succ => [()]
  output
    | .get => .one [()]
    | .put => .one []
    | .succ => .one [()]

abbrev Value : Unit → Type := fun _ => Nat

/-- The runtime: the value of the cell, and the number of the reads. -/
abbrev Cell : Type := Nat × Nat

/-- The machine of the cell. A read gives the value and counts. A write replaces the value. The
successor does not use the runtime. The machine does not stop. -/
def machine : Machine (sig.interface Value) Cell Empty
  | (⟨.get, _⟩, s) => .inr (⟨Boundary.only _, .cons s.1 .nil⟩, (s.1, s.2 + 1))
  | (⟨.put, args⟩, s) => .inr (⟨Boundary.only _, .nil⟩, (args.lookup .here, s.2))
  | (⟨.succ, args⟩, s) => .inr (⟨Boundary.only _, .cons (args.lookup .here + 1) .nil⟩, s)

/-! A read, a kept value, a write, and a second read. -/

abbrev Two : Exits Unit := [.one [(), ()]]

/-- Read the cell, write the successor of the value, and read the cell again. The exit has the
first value and the second value. The first value has two uses. -/
def readWrite : Diagram sig [] Two :=
  .step ⟨.get, .nil⟩ (.one
    (.step ⟨.succ, .cons .here .nil⟩ (.one
      (.step ⟨.put, .cons .here .nil⟩ (.one
        (.step ⟨.get, .nil⟩ (.one
          (.exit ⟨_, .here, Boundary.only _,
            .cons (.there (.there .here)) (.cons .here .nil)⟩))))))))

/-- The two values of the one exit case. -/
def values : Exits.At Two Value → Nat × Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => (out.lookup .here, out.lookup (.there .here))

set_option smartUnfolding false in
/-- The kept value is the first value of the cell, the second read has its successor, and the
run has two reads, for an arbitrary cell. -/
def readWriteRun (n c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    machine.run (readWrite.run stop n .nil fun r => .pure (values r)) (c, k) ≡
      .inr ((c, c + 1), (c + 1, k + 2)) := .refl

/-! A write and a read in the two orders. -/

abbrev One : Exits Unit := [.one [()]]

/-- The value of the one exit case. -/
def value : Exits.At One Value → Nat
  | ⟨_, .here, ⟨_, .here⟩, out⟩ => out.lookup .here

/-- Write the input, and then read the cell. -/
def putGet : Diagram sig [()] One :=
  .step ⟨.put, .cons .here .nil⟩ (.one
    (.step ⟨.get, .nil⟩ (.one (.exit ⟨_, .here, Boundary.only _, .cons .here .nil⟩))))

/-- Read the cell, and then write the input. -/
def getPut : Diagram sig [()] One :=
  .step ⟨.get, .nil⟩ (.one
    (.step ⟨.put, .cons (.there .here) .nil⟩ (.one
      (.exit ⟨_, .here, Boundary.only _, .cons .here .nil⟩))))

/-- The value that a run returns. -/
def observe (d : Diagram sig [()] One) (a : Nat) (s : Cell) : Empty ⊕ (Nat × Cell) :=
  machine.run (d.run (.pure 0) 0 (.cons a .nil) fun r => .pure (value r)) s

set_option smartUnfolding false in
/-- The read after the write has the input. -/
def putGetRun (a c k : Nat) : observe putGet a (c, k) ≡ .inr (a, (a, k + 1)) := .refl

set_option smartUnfolding false in
/-- The read before the write has the first value of the cell. -/
def getPutRun (a c k : Nat) : observe getPut a (c, k) ≡ .inr (c, (a, k + 1)) := .refl

/-- The returned value of an outcome. -/
def returned : Empty ⊕ (Nat × Cell) → Nat
  | .inr b => b.1

/-- A type with a value at a successor only. -/
def Positive : Nat → Type
  | 0 => Empty
  | _ + 1 => Unit

set_option smartUnfolding false in
/-- The two orders give different values from the cell 0 with the input 1. -/
def ordersDiffer (k : Nat) (same : observe putGet 1 (0, k) ≡ observe getPut 1 (0, k)) : Empty :=
  Identity.transport (fun out => Positive (returned out)) same ()

/-! The first diagram with a specification of two runtimes. -/

/-- The condition at the result, for a first cell: the two values, and the last runtime. A
stop has no evidence. -/
def Result (c k : Nat) : Empty ⊕ (Exits.At Two Value × Cell) → Type
  | .inl _ => Empty
  | .inr b => (values b.1 ≡ (c, c + 1)) × (b.2 ≡ (c + 1, k + 2))

set_option smartUnfolding false in
/-- The evidence of the diagram for the graph of the machine, by the constructors of the
diagram. Each step has the response of the machine at its runtime. -/
def readWriteDep (n c k : Nat) :
    readWrite.StateDep machine.graph n (fun r s => Result c k (.inr (r, s)))
      (fun _ => Empty) (fun _ => Empty) .nil (c, k) :=
  Diagram.StateDep.stepResponse (S := sig) machine ⟨Op.get, .nil⟩ _ .refl
    (Diagram.StateDep.stepResponse (S := sig) machine ⟨Op.succ, .cons .here .nil⟩ _ .refl
      (Diagram.StateDep.stepResponse (S := sig) machine ⟨Op.put, .cons .here .nil⟩ _ .refl
        (Diagram.StateDep.stepResponse (S := sig) machine ⟨Op.get, .nil⟩ _ .refl
          (Diagram.StateDep.exit _ (.refl, .refl)))))

set_option smartUnfolding false in
/-- The evidence at the result of the run on the machine. The machine has evidence of its
graph. -/
def readWriteEvidence (n c k : Nat) (stop : Free (sig.interface Value) (Exits.At Two Value)) :
    Result c k (machine.run (readWrite.run stop n .nil .pure) (c, k)) :=
  FreeDep.run machine.graphEvidence
    (readWriteDep n c k (F := Result c k) (stop := stop) (fun e => e.elim) (fun _ e => e.elim)
      (fun _ _ post => .pure post))

set_option smartUnfolding false in
/-- The identity of the last runtime is consumed through a dependent payload, for an arbitrary
cell. -/
def readWriteReads (n c k : Nat) (stop : Free (sig.interface Value) (Exits.At Two Value)) :
    (Identity.transport (fun (s : Cell) => Fin (s.2 + 1)) (readWriteEvidence n c k stop).2
      ⟨k + 2, Nat.lt_succ_self _⟩).val ≡ k + 2 := .refl

/-! A pure step and a read in the two orders, on the machine of a lowering. -/

/-- The calls of the cell: a read, and a write of a value. -/
inductive CellOp where
  | read
  | write (value : Nat)

/-- The interface of the cell. -/
def cell : Container.{0, 0} :=
  ⟨CellOp, fun
    | .read => Nat
    | .write _ => Unit⟩

/-- The machine of the cell. A read gives the value and counts. A write replaces the value. -/
def cellMachine : Machine cell Cell Empty
  | (.read, s) => .inr (s.1, (s.1, s.2 + 1))
  | (.write value, s) => .inr ((), (value, s.2))

/-- The lowering. A read and a write are one call each. The successor returns without a
call. -/
def lower : Impl (sig.interface Value) cell
  | ⟨.get, _⟩ => .request .read fun (value : Nat) => .pure ⟨Boundary.only _, .cons value .nil⟩
  | ⟨.put, args⟩ => .request (.write (args.lookup .here)) fun _ => .pure ⟨Boundary.only _, .nil⟩
  | ⟨.succ, args⟩ => .pure ⟨Boundary.only _, .cons (args.lookup .here + 1) .nil⟩

/-- The machine of the lowering is the machine of the signature. -/
def lowered : Homotopy (cellMachine.impl lower) machine
  | (⟨.get, _⟩, _) => .refl
  | (⟨.put, _⟩, _) => .refl
  | (⟨.succ, _⟩, _) => .refl

/-- The successor returns without a call. -/
def returns : sig.Returns lower
  | .succ, _, args => ⟨⟨Boundary.only _, .cons (args.lookup .here + 1) .nil⟩, .pure .refl⟩

/-- The operand of the successor: the input. -/
def succArgs : PortMap [()] [()] := .cons .here .nil

/-- A read has no operand. -/
def getArgs : PortMap [()] [] := .nil

/-- The exit with the successor and the value of the read. The context has the value of the
read, the successor, and the input. -/
def both : Diagram sig [(), (), ()] Two :=
  .exit ⟨_, .here, Boundary.only _, .cons (.there .here) (.cons .here .nil)⟩

/-- The rest after the two steps, for each pair of their output cases. -/
def after : (ca : (sig.output .succ).Case) → (cb : (sig.output .get).Case) →
    Diagram sig (cb.1 ++ (ca.1 ++ [()])) Two
  | ⟨_, .here⟩, ⟨_, .here⟩ => both

/-- The successor, and then the read. The context of the read has the successor. -/
def succFirst : Diagram sig [()] Two :=
  .step ⟨.succ, succArgs⟩ fun ca => .step ⟨.get, getArgs.weaken _⟩ fun cb => after ca cb

/-- The read, and then the successor. The rest has the two outputs exchanged. -/
def getFirst : Diagram sig [()] Two :=
  .step ⟨.get, getArgs⟩ fun cb => .step ⟨.succ, succArgs.weaken _⟩ fun ca =>
    (after ca cb).rename (PortMap.exchange _ _ _)

/-- The interchange derivation of the pure step. -/
def moved : Diagram.Derivation (.interchange sig) succFirst getFirst :=
  .rule (.swap (S := sig) Op.succ Op.get (.inl .refl) succArgs getArgs after)

/-- The run of a diagram on the machine of the lowering, with the two values. -/
def observed (d : Diagram sig [()] Two) (n : Nat) (stop : Free (sig.interface Value) (Nat × Nat))
    (a : Nat) (s : Cell) : Empty ⊕ ((Nat × Nat) × Cell) :=
  (cellMachine.impl lower).run (d.run stop n (.cons a .nil) fun r => .pure (values r)) s

set_option smartUnfolding false in
/-- The first order has the successor of the input and the value of the cell, and one read. -/
def succFirstRun (n a c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed succFirst n stop a (c, k) ≡ .inr ((a + 1, c), (c, k + 1)) := .refl

/-- The two orders have one run on the machine of the lowering: the run of the derivation. -/
def movedRun (n a : Nat) (s : Cell) (stop : Free (sig.interface Value) (Nat × Nat)) :
    observed succFirst n stop a s ≡ observed getFirst n stop a s :=
  moved.sound stop n ((Rules.Sound.interchange returns).machine cellMachine) (.cons a .nil)
    (fun r => .pure (values r)) s

/-- The number of the reads of a result. -/
def reads : Empty ⊕ ((Nat × Nat) × Cell) → Nat
  | .inr b => b.2.2

set_option smartUnfolding false in
/-- The identity of the two runs is consumed through a dependent payload, for an arbitrary
input and an arbitrary cell. -/
def movedReads (n a c k : Nat) (stop : Free (sig.interface Value) (Nat × Nat)) :
    (Identity.transport (fun out => Fin (reads out + 1)) (movedRun n a (c, k) stop)
      ⟨k + 1, Nat.lt_succ_self _⟩).val ≡ k + 1 := .refl

/-- The specification of the two diagrams with a runtime. A witness of the precondition has a
lower bound of the number of the reads, with the difference. The exit has the two values, and
the difference at the last runtime for the bound of the witness. A stop has no evidence. -/
def counted : DepPoly.{0, 0, 0, 0} ((Diagram.interface Value [()] Two).runtime Cell Empty) where
  Pre a := (b : Nat) × ((j : Nat) × (a.2.2 ≡ b + j))
  Post a pre := fun
    | .inl _ => Empty
    | .inr out =>
        (values out.1 ≡ (a.1.lookup .here + 1, a.2.1)) × ((j : Nat) × (out.2.2 ≡ pre.1 + j))

set_option smartUnfolding false in
/-- The lift of the first order, by the constructors of the diagram. The specification of the
calls is the graph of the machine of the lowering. The exit has the difference of the witness
with one more read. -/
def succLift (n : Nat) :
    succFirst.StateLift (cellMachine.impl lower).graph n counted (fun _ _ _ => Empty) :=
  fun _ _ pre =>
    Diagram.StateDep.stepResponse (S := sig) (cellMachine.impl lower) ⟨Op.succ, succArgs⟩ _ .refl
      (Diagram.StateDep.stepResponse (S := sig) (cellMachine.impl lower)
        ⟨Op.get, getArgs.weaken _⟩ _ .refl
        (Diagram.StateDep.exit _
          (.refl, ⟨pre.2.1 + 1, Identity.cong (fun k => k + 1) pre.2.2⟩)))

variable (stop : Free (sig.interface Value) (Exits.At Two Value)) (count : Nat)

/-- The verified diagram with a runtime, and then the lowering: a verified implementation by
the calls of the cell. The lowering is a verified implementation between the graphs of the two
machines. -/
def succLowered :
    ImplDep counted cellMachine.graph ((succFirst.impl stop count).thread.trans lower.thread) :=
  ((succLift count).impl fun _ _ _ _ e => e.elim).trans (ImplDep.graph lower.thread cellMachine)

/-- The interchange as a map of verified implementations with a runtime. -/
def getLowered :
    ImplDep counted cellMachine.graph ((getFirst.impl stop count).thread.trans lower.thread) :=
  moved.stateLift (.interchange returns) stop count (succLowered stop count)

/-- The difference in the evidence at a result. -/
def difference {a : All Value [()] × Cell} {pre : counted.Pre a} :
    {out : Empty ⊕ (Exits.At Two Value × Cell)} → counted.Post a pre out → Nat
  | .inr _, post => post.2.1

/-- The number of the reads at a result, through the identity in the evidence. -/
def counter {a : All Value [()] × Cell} {pre : counted.Pre a} :
    {out : Empty ⊕ (Exits.At Two Value × Cell)} → counted.Post a pre out → Nat
  | .inr out, post =>
      (Identity.transport (fun k => Fin (k + 1)) post.2.2 ⟨out.2.2, Nat.lt_succ_self _⟩).val

/-- The evidence at the result of the run on the machine of the cell, which has evidence of
its graph. -/
def evidence {f : Impl ((Diagram.interface Value [()] Two).runtime Cell Empty)
      (cell.runtime Cell Empty)}
    (ff : ImplDep counted cellMachine.graph f) (a : Nat) (s : Cell)
    (pre : counted.Pre (.cons a .nil, s)) :
    counted.Post (.cons a .nil, s) pre (f.run cellMachine (.cons a .nil, s)) :=
  ff.run cellMachine.graphEvidence (.cons a .nil, s) pre

set_option smartUnfolding false in
/-- Two witnesses of one runtime give different payloads, for an arbitrary input, an arbitrary
cell, and an arbitrary bound. -/
def succWide (a c b j : Nat) :
    difference (evidence (succLowered stop count) a (c, b + j) ⟨b, j, .refl⟩) ≡ j + 1 := .refl

set_option smartUnfolding false in
def succTight (a c b j : Nat) :
    difference (evidence (succLowered stop count) a (c, b + j) ⟨b + j, 0, .refl⟩) ≡ 1 := .refl

set_option smartUnfolding false in
/-- After the interchange, the evidence of the second order gives the same payloads. -/
def getWide (a c b j : Nat) :
    difference (evidence (getLowered stop count) a (c, b + j) ⟨b, j, .refl⟩) ≡ j + 1 := .refl

set_option smartUnfolding false in
def getTight (a c b j : Nat) :
    difference (evidence (getLowered stop count) a (c, b + j) ⟨b + j, 0, .refl⟩) ≡ 1 := .refl

set_option smartUnfolding false in
/-- The identity of the number of the reads in the moved evidence is consumed through a
dependent payload. -/
def getCounter (a c b j : Nat) :
    counter (evidence (getLowered stop count) a (c, b + j) ⟨b, j, .refl⟩) ≡ b + j + 1 := .refl

/-! The evidence of the machine of a diagram, along a derivation. -/

/-- The interchange rule holds on the machine of the lowering. -/
def onMachine :
    (Rules.interchange sig).Sound (α := Exits.At Two Value) (cellMachine.impl lower).congruence :=
  (Rules.Sound.interchange returns).machine cellMachine

/-- The evidence of the machine of the first order: the run of the verified diagram on the
machine of the lowering, which has evidence of its graph. -/
def succMachine :
    Evidence counted ((cellMachine.impl lower).impl (succFirst.impl stop count)) :=
  ((succLift count).impl fun _ _ _ _ e => e.elim).run (cellMachine.impl lower).graphEvidence

/-- The evidence of the machine of the second order, along the interchange derivation. -/
def getMachine :
    Evidence counted ((cellMachine.impl lower).impl (getFirst.impl stop count)) :=
  moved.evidence onMachine stop count (succMachine stop count)

set_option smartUnfolding false in
/-- The moved evidence gives the payload of each witness, for an arbitrary input, an arbitrary
cell, and an arbitrary bound. -/
def machineWide (a c b j : Nat) :
    difference (getMachine stop count (.cons a .nil, (c, b + j)) ⟨b, j, .refl⟩) ≡ j + 1 := .refl

set_option smartUnfolding false in
def machineTight (a c b j : Nat) :
    difference (getMachine stop count (.cons a .nil, (c, b + j)) ⟨b + j, 0, .refl⟩) ≡ 1 := .refl

set_option smartUnfolding false in
/-- The identity of the number of the reads in the moved evidence is consumed through a
dependent payload. -/
def machineCounter (a c b j : Nat) :
    counter (getMachine stop count (.cons a .nil, (c, b + j)) ⟨b, j, .refl⟩) ≡ b + j + 1 := .refl

end Draft.Checks.State

/-- info: 'Draft.Checks.State.readWriteRun' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.readWriteRun

/-- info: 'Draft.Checks.State.ordersDiffer' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.ordersDiffer

/-- info: 'Draft.Checks.State.readWriteReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.readWriteReads

/-- info: 'Draft.Checks.State.lowered' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.lowered

/-- info: 'Draft.Checks.State.movedReads' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.movedReads

/-- info: 'Draft.Checks.State.succTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.succTight

/-- info: 'Draft.Checks.State.getWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.getWide

/-- info: 'Draft.Checks.State.getTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.getTight

/-- info: 'Draft.Checks.State.getCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.getCounter

/-- info: 'Draft.Checks.State.machineWide' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.machineWide

/-- info: 'Draft.Checks.State.machineTight' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.machineTight

/-- info: 'Draft.Checks.State.machineCounter' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.State.machineCounter
