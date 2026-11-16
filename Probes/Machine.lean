import Draft.Checks.Countdown
import Draft.Checks.Verified

/-! Probe: Aberlé's Mealy machine with an explicit carrier. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

/-- The interface with a state in each request and in each response. -/
def stateful (C : Container.{0, 0}) (R : Type) : Container.{0, 0} :=
  ⟨R × C.Shape, fun a => C.Pos a.2 × R⟩

/-- A machine with the carrier `R`: a response and a next state for each state and each
request. This is `def:mealy` with an explicit carrier, and it is a closed provider of the
interface with the state. -/
abbrev Machine (C : Container.{0, 0}) (R : Type) : Type := Section (stateful C R)

variable {C D : Container.{0, 0}} {R : Type} {α : Type}

/-- The run of a computation on a machine (`run-mealy`). -/
def runOn (m : Machine C R) : Free C α → R → α × R
  | .pure a, s => (a, s)
  | .request a k, s => runOn m (k (m (s, a)).1) (m (s, a)).2

/-- An implementation and a machine for its calls give a machine (`prog→mealy`). -/
def Machine.impl (f : Impl C D) (m : Machine D R) : Machine C R := fun a => runOn m (f a.2) a.1

/-- The specification of a machine from a specification of its interface and an invariant of
its state. Evidence for it is `def:depmealy` with an explicit carrier. -/
def invariantSpec (r : DepPoly.{0, 0, 0, 0} C) (T : R → Type) :
    DepPoly.{0, 0, 0, 0} (stateful C R) where
  Pre a := T a.1 × r.Pre a.2
  Post a pre b := r.Post a.2 pre.2 b.1 × T b.2

/-- The evidence at the result of a run, with the invariant at the last state
(`run-mealyD`). -/
def runOnDep {r : DepPoly.{0, 0, 0, 0} C} {T : R → Type} {m : Machine C R}
    (e : Evidence (invariantSpec r T) m) {Q : α → Type} {x : Free C α} (h : FreeDep r Q x) :
    (s : R) → T s → Q (runOn m x s).1 × T (runOn m x s).2 :=
  FreeDep.casesOn
    (motive := fun x _ => (s : R) → T s → Q (runOn m x s).1 × T (runOn m x s).2) h
    (fun q _ t => (q, t))
    (fun {a k} pre verified s t =>
      runOnDep e (x := k (m (s, a)).1) (verified (m (s, a)).1 (e (s, a) (t, pre)).1)
        (m (s, a)).2 (e (s, a) (t, pre)).2)

/-- A verified implementation and a verified machine give a verified machine
(`prop:prog-mealy-dep`). -/
def Machine.implDep {q : DepPoly.{0, 0, 0, 0} C} {r : DepPoly.{0, 0, 0, 0} D} {T : R → Type}
    {f : Impl C D} {m : Machine D R} (ff : ImplDep q r f)
    (e : Evidence (invariantSpec r T) m) : Evidence (invariantSpec q T) (Machine.impl f m) :=
  fun a pre => runOnDep e (ff a.2 pre.2) a.1 pre.1

/-! Her state effect and her state invariant. -/

inductive StateI (S : Type) : Type where
  | get
  | put (s : S)

def State (S : Type) : Container.{0, 0} :=
  ⟨StateI S, fun
    | .get => S
    | .put _ => Unit⟩

def stateMachine (S : Type) : Machine (State S) S
  | (s, .get) => (s, s)
  | (_, .put s') => ((), s')

def Invariant (S : Type) (T : S → Type) : DepPoly.{0, 0, 0, 0} (State S) where
  Pre
    | .get => Unit
    | .put s => T s
  Post
    | .get, _, s => T s
    | .put _, _, _ => Unit

def invariant (S : Type) (T : S → Type) :
    Evidence (invariantSpec (Invariant S T) T) (stateMachine S)
  | (_, .get), (t, _) => (t, t)
  | (_, .put _), (_, t') => ((), t')

/-- A program that reads the counter and writes its successor. -/
def tick : Impl ⟨Unit, fun _ => Nat⟩ (State Nat) := fun _ =>
  .request .get fun (s : Nat) => .request (.put (s + 1)) fun _ => .pure s

/-- A specification with the two states of a transition: the response is the state before, and
the state after is its successor. An invariant of one state cannot say this. -/
def tickSpec : DepPoly.{0, 0, 0, 0} (stateful ⟨Unit, fun _ => Nat⟩ Nat) where
  Pre _ := Unit
  Post a _ b := (b.1 ≡ a.1) × (b.2 ≡ a.1 + 1)

def tickEvidence : Evidence tickSpec (Machine.impl tick (stateMachine Nat)) :=
  fun _ _ => (.refl, .refl)

end Draft

namespace Draft.Checks.Countdown

open Draft

/-- The function of the calls of the check is a machine with the carrier `Nat`. -/
def machine : Machine (sig.interface Value) Nat := fun a => handle a.2 a.1

/-- The relation of calls of the check is the graph of that machine. -/
def callsGraph (a : (sig.interface Value).Shape) (s : Nat)
    (r : (sig.interface Value).Pos a) (s' : Nat) :
    calls a s r s' ≡ (machine (s, a) ≡ (r, s')) := .refl

set_option smartUnfolding false in
/-- The function meaning with three or more unrollings, run on the machine, has the exit and
the state of the run of the loop, for an arbitrary value, an arbitrary state, and an arbitrary
computation at the limit. -/
def onMachine (k a s : Nat) (stop : Free (sig.interface Value) (Exits.At [Out] Value)) :
    runOn machine (countdown.meaning stop (k + 3) (inputs 2 a)) s ≡
      (out ((s + 1) + (s + a)), s + 2) := .refl

end Draft.Checks.Countdown

#print axioms Draft.Machine.implDep
#print axioms Draft.invariant
#print axioms Draft.tickEvidence
#print axioms Draft.Checks.Countdown.onMachine
