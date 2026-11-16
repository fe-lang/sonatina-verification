import Draft.Checks.Polynomial

/-! Computations and implementations under repeated substitution.
A composite of three implementations calls a family sum of two interfaces. The response of
the first call selects the next call, and a response is the shape of a later call. The checks
run the composite with arbitrary responses, and they eliminate the agreements that the laws of
composition give.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Free

open Container Polynomial

/-- The lower interface: a flag, a number, and a pair of numbers. -/
inductive Key where
  | flag
  | one
  | two

def Reply : Key → Type
  | .flag => Bool
  | .one => Nat
  | .two => Nat × Nat

def store : Container := ⟨Key, Reply⟩

def provider (flag : Bool) (x y : Nat) : Section store
  | .flag => flag
  | .one => x
  | .two => (x, y)

inductive Label where
  | test
  | data

/-- The middle interfaces: a test with a `Bool` response, and the two-branch boundary. -/
def family : Label → Container
  | .test => ⟨Unit, fun _ => Bool⟩
  | .data => boundary

abbrev number : Container := ⟨Nat, fun _ => Nat⟩

abbrev task : Container := ⟨Unit, fun _ => Nat⟩

/-- The response of the test selects the data call. -/
def program : Impl number (sigma family) := fun n =>
  .request ⟨.test, ()⟩ fun
    | false => .request ⟨.data, false⟩ fun (m : Nat) => .pure (n + m)
    | true => .request ⟨.data, true⟩ fun (q : Nat × Nat) => .pure (n + q.1 + q.2)

/-- The test negates the flag. The pair branch makes two calls and exchanges the components. -/
def lower : (l : Label) → Impl (family l) store
  | .test => fun _ => .request .flag fun b => .pure (!b)
  | .data => fun
    | false => .request .one .pure
    | true => .request .two fun q => .request .one fun a => .pure (q.2, a)

/-- The first response is the shape of the second call. -/
def user : Impl task number := fun _ =>
  .request 1 fun a => .request a fun b => .pure (a + b)

def closed : Impl number store := program.trans (Impl.copair lower)

def left : Impl task store := (user.trans program).trans (Impl.copair lower)

def right : Impl task store := user.trans closed

/-- Kernel checks of the two branches with arbitrary responses. -/
def runPair (n x y : Nat) : Identity (closed.run (provider false x y) n) (n + y + x) := .refl

def runSingle (n x y : Nat) : Identity (closed.run (provider true x y) n) (n + x) := .refl

def runSubstitution (flag : Bool) (x y : Nat) :
    Identity (right.run (provider flag x y) ())
      (user.run (closed.run (provider flag x y)) ()) :=
  Impl.runTrans user closed (provider flag x y) ()

/-- The dependent `Fin` payload forces elimination of the identity that an agreement gives. -/
def read {f g : Impl task store} (h : Impl.Agreement f g) (flag : Bool) (x y : Nat) : Nat :=
  (Identity.transport (fun n => Fin (n + 1))
    (Impl.runCongr (provider := provider flag x y) h (fun _ => .refl) ())
    ⟨f.run (provider flag x y) (), Nat.lt_succ_self _⟩).val

def assoc : Impl.Agreement left right := Impl.transAssoc user program (Impl.copair lower)

def units : Impl.Agreement (((Impl.id task).trans right).trans (Impl.id store)) right :=
  (Impl.transId _).trans (Impl.idTrans right)

def congruence : Impl.Agreement right (user.trans ((Impl.id number).trans closed)) :=
  Impl.transCongr (Impl.Agreement.refl user) (Impl.idTrans closed).symm

def assocPair (x y : Nat) :
    Identity (read assoc false x y) ((1 + y + x) + ((1 + y + x) + y + x)) := .refl

def assocSingle (x y : Nat) :
    Identity (read assoc true x y) ((1 + x) + ((1 + x) + x)) := .refl

def unitsPair (x y : Nat) :
    Identity (read units false x y) ((1 + y + x) + ((1 + y + x) + y + x)) := .refl

def unitsSingle (x y : Nat) :
    Identity (read units true x y) ((1 + x) + ((1 + x) + x)) := .refl

def congruencePair (x y : Nat) :
    Identity (read congruence false x y) ((1 + y + x) + ((1 + y + x) + y + x)) := .refl

def congruenceSingle (x y : Nat) :
    Identity (read congruence true x y) ((1 + x) + ((1 + x) + x)) := .refl

/-- The identity of `runTrans` is consumed through the same payload. -/
def consumeRunTrans (x y : Nat) :
    Identity (Identity.transport (fun n => Fin (n + 1)) (runSubstitution false x y)
      ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

-- Compiled observations supplement the kernel consumers above.
#guard closed.run (provider false 3 4) 10 == 17
#guard closed.run (provider true 3 4) 10 == 13
#guard left.run (provider false 3 4) () == 23
#guard right.run (provider true 3 4) () == 11
#guard read assoc false 3 4 == 23
#guard read units true 3 4 == 11

end Draft.Checks.Free

/-- info: 'Draft.Checks.Free.congruencePair' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Free.congruencePair

/-- info: 'Draft.Checks.Free.congruenceSingle' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Free.congruenceSingle

/-- info: 'Draft.Checks.Free.consumeRunTrans' does not depend on any axioms -/
#guard_msgs in
#print axioms Draft.Checks.Free.consumeRunTrans
