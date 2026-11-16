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
values, and the last runtime as a function of the first runtime. -/

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
