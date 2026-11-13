import Prelude

set_option autoImplicit false

open Prelude
open scoped Prelude

namespace PreludeTests.Containers

universe s p u v

def extensionUniverse (C : Container.{s, p}) (α : Type u) : Type (max s p u) := C.Ext α

abbrev pair : Container where
  Shape := Unit
  Pos _ := Bool

def values : pair.Ext Nat := ⟨(), fun b => if b then 11 else 7⟩

-- Morphisms may select or repeat a position.
def first : Container.Hom pair Container.identity where
  shape _ := ()
  position _ _ := false

def duplicate : Container.Hom Container.identity pair where
  shape _ := ()
  position _ _ := ()

#guard ((first.trans duplicate).apply values).2 false == 7
#guard ((first.trans duplicate).apply values).2 true == 7
#guard ((fun n => n + 1) <$> values).2 true == 12

-- Mapping also crosses universe levels.
def mapAcrossUniverses : (pair.map (fun n => Fin n) values).2 true ≡ Fin 11 := .refl

abbrev sequence : Container where
  Shape := Nat
  Pos := Fin

def nested : sequence.Ext (sequence.Ext Nat) :=
  ⟨2, fun i => if i.val = 0 then ⟨0, Fin.elim0⟩ else ⟨3, fun j => j.val + 10⟩⟩

def flattened := Container.flatten nested

#guard flattened.2 ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩ == 12
#guard ((Container.unflatten flattened).2 ⟨0, by decide⟩).1 == 0
#guard ((Container.unflatten flattened).2 ⟨1, by decide⟩).1 == 3

-- Sum and product preserve their component values, including empty positions.
def tagged : (sequence.sum pair).Ext Nat := Container.sumIn (.inr values)

#guard match Container.sumOut tagged with
  | .inl _ => false
  | .inr x => x.2 true == 11

def paired : (sequence.product pair).Ext Nat :=
  Container.productIn (⟨0, Fin.elim0⟩, values)

#guard (Container.productOut paired).1.1 == 0
#guard paired.2 (.inr true) == 11

-- Position universes can differ across a sum.
abbrev typePorts : Container.{0, 1} where
  Shape := Unit
  Pos _ := Type

def mixed : (pair.sum typePorts).Ext Nat :=
  Container.sumIn (.inr ⟨(), fun _ => 23⟩)

def mixedSumRoundTrip : Container.sumOut mixed ≡ .inr ⟨(), fun _ => 23⟩ := .refl

-- The round trips of the sum and of the composite are `.refl` at arbitrary extensions.
def sumRoundTrip (x : pair.Ext Nat) :
    (Container.sumIso (C := sequence) (D := pair)).invTo (.inr x) ≡ .refl := .refl

def sumRoundTripBack (n : Nat) (f : Fin n → Nat) :
    (Container.sumIso (C := sequence) (D := pair)).toInv ⟨.inl n, fun i => f i.down⟩ ≡ .refl :=
  .refl

def compRoundTrip (x : sequence.Ext (sequence.Ext Nat)) :
    (Container.compIso (C := sequence) (D := sequence)).invTo x ≡ .refl := .refl

def compRoundTripBack (x : (sequence.comp sequence).Ext Nat) :
    (Container.compIso (C := sequence) (D := sequence)).toInv x ≡ .refl := .refl

/-- An agreement between two extensions that are not syntactically equal. -/
def addZero (f : Bool → Nat) :
    Container.Ext.Agreement pair (⟨(), f⟩ : pair.Ext Nat) ⟨(), fun b => f b + 0⟩ :=
  ⟨.refl, fun _ => .refl⟩

-- Symmetry and composition of agreements give value witnesses that reduce to `.refl`.
def symmValue (f : Bool → Nat) (b : Bool) : (addZero f).symm.values b ≡ .refl := .refl

def transValue (f : Bool → Nat) (b : Bool) :
    ((addZero f).trans (addZero _)).values b ≡ .refl := .refl

def transSymmValue (f : Bool → Nat) (b : Bool) :
    (((addZero f).trans (addZero _)).trans ((addZero f).trans (addZero _)).symm).values b ≡
      .refl := .refl

-- Evidence at each position moves along a composed agreement into a dependent payload.
def allValue (f : Bool → Nat) (b : Bool) :
    (((addZero f).trans (addZero _)).all (fun n => Fin (n + 1))
      (fun i => ⟨0, Nat.zero_lt_succ (f i)⟩) b).val ≡ 0 := .refl

def constantIndexedExtension (C : Container.{s, p}) (α : Type u) (x : C.Ext α) :
    C.indexed.Ext (fun _ => α) () := x

inductive Ty where
  | nat
  | bool

abbrev Ty.denote : Ty → Type
  | .nat => Nat
  | .bool => Bool

inductive Op : Ty → Type where
  | add : Op .nat
  | select (t : Ty) : Op t

abbrev typed : IndexedContainer Ty Ty where
  Shape := Op
  Pos
    | .add => Bool
    | .select _ => Option Bool
  index s := match s with
    | .add => fun _ => .nat
    | .select t => fun p => match p with
      | none => .bool
      | some _ => t

abbrev context : List Ty := [.nat, .bool, .nat]

def environment : All Ty.denote context := .cons 7 (.cons true (.cons 11 .nil))

def selection : typed.Ext (fun t => Elem t context) .nat :=
  ⟨.select .nat, fun p => match p with
    | none => .there .here
    | some false => .here
    | some true => .there (.there .here)⟩

def resolved : typed.Ext Ty.denote .nat :=
  typed.map (fun _ ref => environment.lookup ref) selection

#guard resolved.2 none
#guard Nat.beq (resolved.2 (some false)) 7
#guard Nat.beq (resolved.2 (some true)) 11

def shared : typed.Ext (fun t => Elem t context) .nat := ⟨.add, fun _ => .here⟩

#guard Nat.beq ((typed.map (fun _ ref => environment.lookup ref) shared).2 false) 7
#guard Nat.beq ((typed.map (fun _ ref => environment.lookup ref) shared).2 true) 7

-- Boolean values cannot fill the natural-number ports of this shape.
def rejectWrongPortType : True := by
  fail_if_success
    let invalid : typed.Ext Ty.denote .nat := ⟨.select .nat, fun _ => true⟩
  trivial

def swapAdd : IndexedContainer.Hom typed typed where
  shape _ s := s
  position s p := match s with
    | .add => !p
    | .select _ => p
  index s _ := by cases s <;> exact .refl

def addValues : typed.Ext Ty.denote .nat := ⟨.add, fun b => if b then 11 else 7⟩

#guard Nat.beq ((swapAdd.apply addValues).2 false) 11
#guard Nat.beq ((swapAdd.apply addValues).2 true) 7
#guard Nat.beq (((swapAdd.trans swapAdd).apply addValues).2 true) 11

def withIdentity : typed.Ext ((IndexedContainer.identity Ty).Ext Ty.denote) .nat :=
  typed.map (fun _ value => ⟨(), fun _ => value⟩) resolved

def typedFlat := IndexedContainer.flatten withIdentity

#guard typedFlat.2 ⟨none, ()⟩
#guard Nat.beq (typedFlat.2 ⟨some true, ()⟩) 11

-- The input indices of a morphism need only be propositionally equal.
def slot (n : Nat) : IndexedContainer Nat Unit where
  Shape _ := Unit
  Pos _ := Unit
  index _ _ := n

def zeroAdd : (n : Nat) → 0 + n ≡ n
  | 0 => .refl
  | n + 1 => Identity.cong Nat.succ (zeroAdd n)

def succAdd (n : Nat) : (m : Nat) → (n + 1) + m ≡ (n + m) + 1
  | 0 => .refl
  | m + 1 => Identity.cong Nat.succ (succAdd n m)

def addComm (n : Nat) : (m : Nat) → n + m ≡ m + n
  | 0 => (zeroAdd n).symm
  | m + 1 => (Identity.cong Nat.succ (addComm n m)).trans (succAdd m n).symm

def commute (n m : Nat) : IndexedContainer.Hom (slot (n + m)) (slot (m + n)) where
  shape _ _ := ()
  position _ _ := ()
  index _ _ := addComm n m

def retag {n m : Nat} (x : Fin (n + m)) : Fin (m + n) :=
  ((commute n m).apply (X := Fin) (o := ()) ⟨(), fun _ => x⟩).2 ()

#guard (retag (n := 2) (m := 3) ⟨4, by decide⟩).val == 4

def retagComputes : Identity (retag (n := 2) (m := 3) ⟨4, by decide⟩).val 4 := .refl

def indexedNaturality {X : Nat → Type u} {Y : Nat → Type v}
    (f : (i : Nat) → X i → Y i) (n m : Nat) (x : (slot (n + m)).Ext X ()) :
    IndexedContainer.Ext.Agreement (slot (m + n))
      ((commute n m).apply ((slot (n + m)).map f x))
      ((slot (m + n)).map f ((commute n m).apply x)) :=
  (commute n m).natural f x

namespace FreeChecks

/-- A family with its index in `Type 1`: each type is an interface with one shape for each
value, and the response is a value of that type. -/
def each : Type → Container.{0, 0} := fun A => ⟨A, fun _ => A⟩

def all : Container.{1, 0} := Container.sigma each

def echo : Container.Section all := fun a => a.2

/-- Shapes in `Type 1`, positions in `Type`, and a returned value in `Type 1`. -/
def pick : Container.Free all Type :=
  .request ⟨Bool, true⟩ fun (b : Bool) =>
    match b with
    | true => .pure Nat
    | false => .pure Unit

def pickRun : Identity (pick.run echo) Nat := .refl

def twice : (A : Type) → Container.Impl (each A) all :=
  fun A a => .request ⟨A, a⟩ fun b => .request ⟨A, b⟩ .pure

def joined : Container.Impl all all := Container.Impl.copair twice

def joinedRun (A : Type) (a : A) : Identity (joined.run echo ⟨A, a⟩) a := .refl

def substituted (A : Type) (a : A) :
    Identity ((joined.trans joined).run echo ⟨A, a⟩) (joined.run (joined.run echo) ⟨A, a⟩) :=
  Container.Impl.runTrans joined joined echo ⟨A, a⟩

def inclusion (A : Type) :
    Identity ((Container.Hom.inj each A).trans (Container.Hom.copair (Container.Hom.inj each)))
      (Container.Hom.inj each A) := .refl

/-- A specification with its admissions in `Type 1`. An admission is a type, and the response
of a call is identical to the value of its shape. -/
def echoSpec : Container.DepPoly all where
  Pre _ := Type
  Post a _ response := Identity response a.2

def echoEvidence : Container.Evidence echoSpec echo := fun _ _ => .refl

/-- Each response is the shape of the next call, and the evidence composes the two
identities. -/
def twiceDep (A : Type) (a : A) :
    Container.FreeDep echoSpec (fun b => Identity b a) (twice A a) :=
  .request Nat fun _ first => .request Unit fun _ second => .pure (second.trans first)

def twiceDepRun (A : Type) (a : A) : Identity ((twiceDep A a).run echoEvidence) .refl := .refl

/-- A bind passes the evidence of the first computation to the second computation. -/
def boundDep (A : Type) (a : A) :
    Container.FreeDep echoSpec (fun b => Identity b a) ((twice A a).bind (twice A)) :=
  (twiceDep A a).bind fun b same =>
    Identity.transport (fun c => Container.FreeDep echoSpec (fun d => Identity d c) (twice A b))
      same (twiceDep A b)

def boundDepRun (A : Type) (a : A) : Identity ((boundDep A a).run echoEvidence) .refl := .refl

def movedDepRun (A : Type) (a : A) :
    Identity
      (((boundDep A a).bind (fun _ same => .pure same)).reindex
        (Container.Free.bindPure ((twice A a).bind (twice A)))
        |>.run echoEvidence) .refl := .refl

/-- info: 'Prelude.Container.FreeDep.bind' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.FreeDep.bind

/-- info: 'Prelude.Container.FreeDep.runBind' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.FreeDep.runBind

/-- info: 'Prelude.Container.FreeDep.runReindex' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.FreeDep.runReindex

/-- The specification of each interface of the family. Their family sum is `echoSpec`. -/
def eachSpec (A : Type) : Container.DepPoly (each A) :=
  ⟨fun _ => Type, fun a _ response => Identity response a⟩

def twiceLift (A : Type) : Container.ImplDep (eachSpec A) echoSpec (twice A) :=
  fun _ _ => .request Nat fun _ first => .request Unit fun _ second =>
    .pure (second.trans first)

/-- The lift of the copairing, and the lift of its composite with itself. -/
def joinedLift : Container.ImplDep (Container.DepPoly.sigma eachSpec) echoSpec joined :=
  Container.ImplDep.copair twiceLift

def composedRun (A : Type) (a : A) :
    Identity ((joinedLift.trans (t := echoSpec) joinedLift).run echoEvidence ⟨A, a⟩ Nat)
      .refl := .refl

/-- info: 'Prelude.Container.FreeDep.runSubst' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.FreeDep.runSubst

/-- info: 'Prelude.Container.ImplDep.runTrans' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.ImplDep.runTrans

/-- An implementation without a call, over the polynomial with no shape in `Type 1`. Its lift
needs no evidence of a provider. -/
def still (A : Type) : Container.Impl (each A) Container.zero.{1, 0} := fun a => .pure a

def stillRun (A : Type) (a : A) : Identity ((still A).run Container.Section.zero a) a := .refl

def stillLift (A : Type) :
    Container.ImplDep (eachSpec A) Container.DepPoly.zero.{1, 0, 0, 0} (still A) :=
  fun _ _ => .pure .refl

def stillLiftRun (A : Type) (a : A) :
    Identity ((stillLift A).run (Container.Evidence.zero _) a Nat) .refl := .refl

/-- A shape that returns without a call gives its response to the continuation. -/
def stillReturns (A : Type) (a : A) : (still A).Returns a := ⟨a, .pure .refl⟩

def stillBind (A : Type) (a : A) (k : A → Container.Free Container.zero.{1, 0} Nat) :
    Container.Free.Agreement (((still A) a).bind k) (k a) := (stillReturns A a).bind k

def stillBindRun (A : Type) (a : A) (n : Nat) :
    (Identity.transport (fun k => Fin (k + 1))
      (((stillBind A a fun _ => .pure n).trans (.pure .refl)).run
        (f := Container.Section.zero) (fun _ => .refl))
      ⟨n, Nat.lt_succ_self _⟩).val ≡ n := .refl

/-- info: 'Prelude.Container.Free.substTrans' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.Free.substTrans

/-- info: 'Prelude.Container.Free.Agreement.trans' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.Free.Agreement.trans

/-- info: 'Prelude.Container.Free.Agreement.run' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.Free.Agreement.run

end FreeChecks

/-- info: 'Prelude.Container.Hom.natural' does not depend on any axioms -/
#guard_msgs in
#print axioms Container.Hom.natural

/-- info: 'Prelude.IndexedContainer.flattenUnflatten' does not depend on any axioms -/
#guard_msgs in
#print axioms IndexedContainer.flattenUnflatten

/-- info: 'Prelude.IndexedContainer.Hom.natural' does not depend on any axioms -/
#guard_msgs in
#print axioms IndexedContainer.Hom.natural

end PreludeTests.Containers
