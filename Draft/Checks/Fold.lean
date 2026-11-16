import Draft.Checks.Verified

/-! A fold on lists as an implementation, with its verification by induction. This is
Aberlé's `fold` and `foldInd`, with append and concat as instances. The fold calls a base
interface and a step interface. Its lift gives the postcondition of the whole list from a
specification of the base and of the step. Append and concat have relational specifications,
and concat calls append in its step. The checks eliminate the relational evidence and recover
the lists.

A third instance calls the store in its base and in each step. The witness of its precondition
is the admission of the first call, and the receipt of each call is the key of the admission
of the next call.

The fold has two forms. `fold` binds the fold of the tail, as Aberlé's `fold` does, and its
binds nest to the left. `foldDirect` gives each call with the calls after it in its
continuation. The two forms agree, and a lift moves along the agreement.
-/

set_option autoImplicit false
set_option genInjectivity false
set_option smartUnfolding false

open Prelude

namespace Draft.Checks.Fold

open Container

/-- A fold of a list of `B` from an `A` to a `C`. -/
def Fold (A B C : Type) : Container := ⟨A × List B, fun _ => C⟩

/-- The result for the empty list. -/
def Base (A C : Type) : Container := ⟨A, fun _ => C⟩

/-- The result for one more element, from the element and the result of the tail. -/
def Step (A B C : Type) : Container := ⟨A × B × C, fun _ => C⟩

inductive Label where
  | base
  | step

def parts (A B C : Type) : Label → Container
  | .base => Base A C
  | .step => Step A B C

section fold

variable {A B C : Type}

def foldAt (a : A) : List B → Free (sigma (parts A B C)) C
  | [] => .request ⟨.base, a⟩ .pure
  | b :: bs => (foldAt a bs).bind fun c => .request ⟨.step, (a, b, c)⟩ .pure

/-- One call of the base, then one call of the step for each element, from the last element
to the first element. -/
def fold : Impl (Fold A B C) (sigma (parts A B C)) := fun x => foldAt x.1 x.2

/-- The fold with its continuation. Each call has the calls after it in its continuation, and
no bind is necessary. -/
def foldThen {γ : Type} (a : A) :
    List B → (C → Free (sigma (parts A B C)) γ) → Free (sigma (parts A B C)) γ
  | [], k => .request ⟨.base, a⟩ k
  | b :: bs, k => foldThen a bs (fun c => .request ⟨.step, (a, b, c)⟩ k)

/-- The fold that gives its calls in sequence, without a bind. -/
def foldDirect : Impl (Fold A B C) (sigma (parts A B C)) := fun x => foldThen x.1 x.2 .pure

/-- The fold with a continuation agrees with the bind of the fold. -/
def foldThenBind {γ : Type} (a : A) : (bs : List B) → (k : C → Free (sigma (parts A B C)) γ) →
    Free.Agreement (foldThen a bs k) ((foldAt a bs).bind k)
  | [], k => .refl (foldThen a [] k)
  | b :: bs, k =>
      (foldThenBind a bs (fun c => .request ⟨.step, (a, b, c)⟩ k)).trans
        (Free.bindAssoc (fun c => Free.call (C := sigma (parts A B C)) ⟨.step, (a, b, c)⟩) k
          (foldAt a bs)).symm

def foldAgreement : Impl.Agreement (foldDirect (A := A) (B := B) (C := C)) fold :=
  fun x => (foldThenBind x.1 x.2 .pure).trans (Free.bindPure (foldAt x.1 x.2))

variable (D : A → Type) (E : (a : A) → D a → List B → C → Type)

/-- The precondition `D` on the initial value, and the postcondition `E` that relates the
initial value, the witness, the list, and the result. -/
def FoldSpec : DepPoly (Fold A B C) where
  Pre x := D x.1
  Post x d c := E x.1 d x.2 c

def BaseSpec : DepPoly (Base A C) where
  Pre a := D a
  Post a d c := E a d [] c

/-- The step has the witness, a list, and the evidence of the postcondition for that list. It
gives the postcondition for the list with one more element. -/
def StepSpec : DepPoly (Step A B C) where
  Pre x := (d : D x.1) × (bs : List B) × E x.1 d bs x.2.2
  Post x pre c := E x.1 pre.1 (x.2.1 :: pre.2.1) c

def partSpecs : (l : Label) → DepPoly (parts A B C l)
  | .base => BaseSpec D E
  | .step => StepSpec D E

variable {D E}

def foldIndAt (a : A) (d : D a) :
    (bs : List B) → FreeDep (DepPoly.sigma (partSpecs D E)) (E a d bs) (foldAt a bs)
  | [] => .request d fun _ e => .pure e
  | _ :: bs => (foldIndAt a d bs).bind fun _ e => .request ⟨d, bs, e⟩ fun _ e' => .pure e'

/-- Induction on the list: the lift of the fold, from the specifications of its two parts. -/
def foldInd : ImplDep (FoldSpec D E) (DepPoly.sigma (partSpecs D E)) fold :=
  fun x d => foldIndAt x.1 d x.2

def foldIndThen {γ : Type} {Q : γ → Type} (a : A) (d : D a) :
    (bs : List B) → {k : C → Free (sigma (parts A B C)) γ} →
      ((c : C) → E a d bs c → FreeDep (DepPoly.sigma (partSpecs D E)) Q (k c)) →
      FreeDep (DepPoly.sigma (partSpecs D E)) Q (foldThen a bs k)
  | [], _, kk => .request d kk
  | _ :: bs, _, kk => foldIndThen a d bs (fun _ e => .request ⟨d, bs, e⟩ kk)

/-- The lift of the fold without a bind. -/
def foldIndDirect : ImplDep (FoldSpec D E) (DepPoly.sigma (partSpecs D E)) foldDirect :=
  fun x d => foldIndThen x.1 d x.2 (fun _ e => .pure e)

end fold

section append

variable {A : Type}

/-- `Append ys u xs zs`: the list `zs` has the elements of `xs` and then the elements of
`ys`. -/
inductive Append (ys : List A) (u : Unit) : List A → List A → Type where
  | nil : Append ys u [] ys
  | cons {xs zs : List A} {x : A} (rest : Append ys u xs zs) : Append ys u (x :: xs) (x :: zs)

/-- The list that the evidence gives when `base` is in the position of the second list. -/
def Append.build (base : List A) {ys : List A} {u : Unit} {xs zs : List A}
    (e : Append ys u xs zs) : List A :=
  Append.casesOn (motive := fun _ _ _ => List A) e base
    (fun {_ _ x} rest => x :: rest.build base)

/-- The related list is the append of the two lists. -/
def Append.sound {ys : List A} {u : Unit} {xs zs : List A} (e : Append ys u xs zs) :
    zs ≡ xs ++ ys :=
  Append.casesOn (motive := fun xs zs _ => zs ≡ xs ++ ys) e .refl
    (fun {_ _ x} rest => Identity.cong (fun l => x :: l) rest.sound)

def appendParts : (l : Label) → Impl (parts (List A) A (List A) l) zero.{0, 0}
  | .base => fun ys => .pure ys
  | .step => fun x => .pure (x.2.1 :: x.2.2)

def append : Impl (Fold (List A) A (List A)) zero.{0, 0} :=
  fold.trans (Impl.copair appendParts)

abbrev AppendSpec : DepPoly (Fold (List A) A (List A)) := FoldSpec (fun _ => Unit) Append

def appendPartsDep : (l : Label) →
    ImplDep (partSpecs (fun _ => Unit) Append l) DepPoly.zero.{0, 0, 0, 0} (appendParts (A := A) l)
  | .base => fun _ _ => .pure .nil
  | .step => fun _ pre => .pure (.cons pre.2.2)

def appendDep : ImplDep AppendSpec DepPoly.zero.{0, 0, 0, 0} (append (A := A)) :=
  foldInd.trans (ImplDep.copair appendPartsDep)

/-- The appended list, from a run without a call. -/
def appended (ys xs : List A) : List A := append.run Section.zero (ys, xs)

/-- The evidence of the appended list. -/
def appendedDep (ys xs : List A) : Append ys () xs (appended ys xs) :=
  appendDep.run (Evidence.zero _) (ys, xs) ()

end append

section concat

variable {A : Type}

/-- `Concat a u xss zs`: the list `zs` has the elements of each list of `xss`, in sequence.
Each step has the evidence of its append. -/
inductive Concat (a u : Unit) : List (List A) → List A → Type where
  | nil : Concat a u [] []
  | cons {xs : List A} {xss : List (List A)} {ys zs : List A}
      (rest : Concat a u xss ys) (joined : Append ys () xs zs) : Concat a u (xs :: xss) zs

/-- The list that the evidence gives. Each step builds on the list of the steps after it. -/
def Concat.build {a u : Unit} {xss : List (List A)} {zs : List A} (e : Concat a u xss zs) :
    List A :=
  Concat.casesOn (motive := fun _ _ _ => List A) e []
    (fun {_ _ _ _} rest joined => joined.build rest.build)

/-- The step of concat calls append with the result of the tail as the second list. -/
def concatStep : Impl (Step Unit (List A) (List A)) (Fold (List A) A (List A)) :=
  fun x => .request (x.2.2, x.2.1) .pure

def concatParts : (l : Label) → Impl (parts Unit (List A) (List A) l) zero.{0, 0}
  | .base => fun _ => .pure []
  | .step => concatStep.trans append

def concat : Impl (Fold Unit (List A) (List A)) zero.{0, 0} :=
  fold.trans (Impl.copair concatParts)

abbrev ConcatSpec : DepPoly (Fold Unit (List A) (List A)) := FoldSpec (fun _ => Unit) Concat

def concatStepDep :
    ImplDep (StepSpec (fun _ => Unit) Concat) AppendSpec (concatStep (A := A)) :=
  fun _ pre => .request () fun _ joined => .pure (.cons pre.2.2 joined)

def concatPartsDep : (l : Label) →
    ImplDep (partSpecs (fun _ => Unit) Concat l) DepPoly.zero.{0, 0, 0, 0} (concatParts (A := A) l)
  | .base => fun _ _ => .pure .nil
  | .step => concatStepDep.trans appendDep

def concatDep : ImplDep ConcatSpec DepPoly.zero.{0, 0, 0, 0} (concat (A := A)) :=
  foldInd.trans (ImplDep.copair concatPartsDep)

def concatenated (xss : List (List A)) : List A := concat.run Section.zero ((), xss)

def concatenatedDep (xss : List (List A)) : Concat () () xss (concatenated xss) :=
  concatDep.run (Evidence.zero _) ((), xss) ()

end concat

section tally

open Dependent (Admission Receipt expected)
open Free (store provider)
open Verified (spec verify)

/-- `Chain d bs c key`: the result `c` of the fold of `bs`, with the receipt of each call. The
first admission is the witness `d`. The admission of each later call has the receipt of the
call before it as its key, and `key` is the last receipt. -/
inductive Chain (d : Admission) : List Nat → Nat → Nat → Type where
  | nil {m : Nat} (receipt : Receipt (expected d m)) : Chain d [] m receipt.actual
  | cons {bs : List Nat} {c key b m : Nat} (rest : Chain d bs c key)
      (receipt : Receipt (expected (.first key) m)) :
      Chain d (b :: bs) (b + m + c) receipt.actual

/-- The sum of the payloads of the receipts. -/
def Chain.total {d : Admission} {bs : List Nat} {c key : Nat} (e : Chain d bs c key) : Nat :=
  Chain.casesOn (motive := fun _ _ _ _ => Nat) e
    (fun receipt => receipt.read)
    (fun rest receipt => receipt.read + rest.total)

abbrev Tallied (_ : Unit) (d : Admission) (bs : List Nat) (c : Nat) : Type :=
  (key : Nat) × Chain d bs c key

/-- The base reads a number. Each step reads a number, and adds it to its element and to the
result of the tail. -/
def tallyParts : (l : Label) → Impl (parts Unit Nat Nat l) store
  | .base => fun _ => .request .one .pure
  | .step => fun x => .request .one fun (m : Nat) => .pure (x.2.1 + m + x.2.2)

def tally : Impl (Fold Unit Nat Nat) store := fold.trans (Impl.copair tallyParts)

def tallyPartsDep :
    (l : Label) → ImplDep (partSpecs (fun _ => Admission) Tallied l) spec (tallyParts l)
  | .base => fun _ d => .request d fun _ receipt => .pure ⟨receipt.actual, .nil receipt⟩
  | .step => fun _ pre => .request (.first pre.2.2.1) fun _ receipt =>
      .pure ⟨receipt.actual, .cons pre.2.2.2 receipt⟩

def tallyDep : ImplDep (FoldSpec (fun _ => Admission) Tallied) spec tally :=
  foldInd.trans (ImplDep.copair tallyPartsDep)

/-- The payload of the chain, from a run of the lift. -/
def consumeTally (flag : Bool) (x y : Nat) (bs : List Nat) (d : Admission) : Nat :=
  (tallyDep.run (verify flag x y) ((), bs) d).2.total

/-- The tally on the fold without a bind. -/
def tallyDirect : Impl (Fold Unit Nat Nat) store := foldDirect.trans (Impl.copair tallyParts)

def tallyDirectDep : ImplDep (FoldSpec (fun _ => Admission) Tallied) spec tallyDirect :=
  foldIndDirect.trans (ImplDep.copair tallyPartsDep)

def consumeTallyDirect (flag : Bool) (x y : Nat) (bs : List Nat) (d : Admission) : Nat :=
  (tallyDirectDep.run (verify flag x y) ((), bs) d).2.total

def tallyAgreement : Impl.Agreement tallyDirect tally :=
  Impl.transCongr foldAgreement (Impl.Agreement.refl (Impl.copair tallyParts))

/-- The lift of the fold without a bind, moved to the fold with binds. -/
def tallyMovedDep : ImplDep (FoldSpec (fun _ => Admission) Tallied) spec tally :=
  tallyDirectDep.reindex tallyAgreement

def consumeTallyMoved (flag : Bool) (x y : Nat) (bs : List Nat) (d : Admission) : Nat :=
  (tallyMovedDep.run (verify flag x y) ((), bs) d).2.total

end tally

section checks

variable {A : Type}

/-- Kernel checks of append with arbitrary elements and an arbitrary second list. -/
def appendRun (a b c : A) (ys : List A) :
    Identity (appended ys [a, b, c]) (a :: b :: c :: ys) := .refl

/-- The evidence gives the appended list on an arbitrary base. -/
def appendBuild (a b c : A) (ys base : List A) :
    Identity ((appendedDep ys [a, b, c]).build base) (a :: b :: c :: base) := .refl

/-- The identity that the evidence gives is consumed through a dependent payload. -/
def appendSound (a b c : A) (ys : List A) :
    Identity (Identity.transport (fun l => Fin (l.length + 1))
      (appendedDep ys [a, b, c]).sound ⟨0, Nat.zero_lt_succ _⟩).val 0 := .refl

/-- Kernel checks of concat with arbitrary elements. The second list is empty. -/
def concatRun (a b c d : A) :
    Identity (concatenated [[a, b], [], [c, d]]) [a, b, c, d] := .refl

def concatBuild (a b c d : A) :
    Identity (concatenatedDep [[a, b], [], [c, d]]).build [a, b, c, d] := .refl

open Dependent (Admission) in
open Free (provider) in
/-- Kernel checks of the tally with arbitrary elements, responses, and keys. -/
def tallyRun (flag : Bool) (p q x y : Nat) :
    Identity (α := Nat) (tally.run (provider flag x y) ((), [p, q])) (p + x + (q + x + x)) :=
  .refl

/-- The two admission constructors for one input give different payloads. Each receipt of the
chain has the receipts before it in its key. -/
def tallyFirst (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTally flag x y [p, q] (.first key))
      (x + (x + (x + key)) + (x + (x + key) + (x + key))) := .refl

def tallySecond (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTally flag x y [p, q] (.second key))
      (x + (x + (key + x + 1)) + (x + (key + x + 1) + (key + x + 1))) := .refl

/-- The fold without a bind gives the same payloads, and its lift gives them after it moves
along the agreement of the two folds. -/
def tallyDirectFirst (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTallyDirect flag x y [p, q] (.first key))
      (x + (x + (x + key)) + (x + (x + key) + (x + key))) := .refl

def tallyDirectSecond (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTallyDirect flag x y [p, q] (.second key))
      (x + (x + (key + x + 1)) + (x + (key + x + 1) + (key + x + 1))) := .refl

def tallyMovedFirst (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTallyMoved flag x y [p, q] (.first key))
      (x + (x + (x + key)) + (x + (x + key) + (x + key))) := .refl

def tallyMovedSecond (flag : Bool) (p q x y key : Nat) :
    Identity (consumeTallyMoved flag x y [p, q] (.second key))
      (x + (x + (key + x + 1)) + (x + (key + x + 1) + (key + x + 1))) := .refl

end checks

-- Compiled observations supplement the kernel consumers above.
#guard appended [4, 5] [1, 2, 3] == [1, 2, 3, 4, 5]
#guard (appendedDep [4, 5] [1, 2, 3]).build [] == [1, 2, 3]
#guard concatenated [[1, 2], [], [3], [4, 5]] == [1, 2, 3, 4, 5]
#guard (concatenatedDep [[1, 2], [], [3], [4, 5]]).build == [1, 2, 3, 4, 5]
#guard (show Nat from tally.run (Free.provider true 3 4) ((), [10, 20])) == 39
#guard consumeTally true 3 4 [10, 20] (.first 5) == 33
#guard consumeTally true 3 4 [10, 20] (.second 5) == 36
#guard consumeTallyDirect true 3 4 [10, 20] (.first 5) == 33
#guard consumeTallyMoved true 3 4 [10, 20] (.second 5) == 36

end Draft.Checks.Fold
