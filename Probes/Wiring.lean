import Draft.Checks.Diagram
import Draft.Checks.Countdown

/-! Probe: the wiring of a diagram, as a morphism of `W′` with a box for each step. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

variable {Ty : Type}

/-- The label of a box: its operation, and its bypass polynomial as a type of cases with a
context for each case. -/
structure Label (S : Signature Ty) where
  op : S.Op
  Case : Type
  ports : Case → List Ty

/-- The bypass of a step: one case, with the context of the step. -/
def Label.step (S : Signature Ty) (o : S.Op) (Γ : List Ty) : Label S := ⟨o, Unit, fun _ => Γ⟩

/-- The product of a boundary and the bypass of a box. -/
def Label.whisker {S : Signature Ty} (M : Boundary Ty) (l : Label S) : Label S :=
  ⟨l.op, M.Case × l.Case, fun p => l.ports p.2 ++ p.1.1⟩

/-- A map of `Poly_*` from the representable of `Δ` to the target polynomial of a wiring: the
undefined alternative, a case of the exits, or the input of a box with a case of its bypass.
Each has a port of `Δ` for each of its ports. -/
inductive Target (S : Signature Ty) {B : Type} (l : B → Label S) (Qs : Exits Ty)
    (Δ : List Ty) : Type where
  | undefined : Target S l Qs Δ
  | exit (out : Qs.At (Port Δ)) : Target S l Qs Δ
  | enter (b : B) (j : (l b).Case) (kept : PortMap Δ ((l b).ports j))
      (args : PortMap Δ (S.input (l b).op)) : Target S l Qs Δ

namespace Target

variable {S : Signature Ty} {B : Type} {l : B → Label S} {Qs : Exits Ty}

/-- Composition with a port map. -/
def rename {Γ Δ : List Ty} (ρ : PortMap Γ Δ) : Target S l Qs Δ → Target S l Qs Γ
  | .undefined => .undefined
  | .exit out => .exit (out.select ρ)
  | .enter b j kept args => .enter b j (ρ.select kept) (ρ.select args)

/-- Composition along the first boundary of the exits. -/
def bindHead {K : Boundary Ty} {Δ : List Ty} (h : (c : K.Case) → Target S l Qs c.1) :
    Target S l (K :: Qs) Δ → Target S l Qs Δ
  | .undefined => .undefined
  | .exit out =>
      Exits.At.elim (X := Port Δ) (fun k => (h k.1).rename k.2) (fun q => .exit q) out
  | .enter b j kept args => .enter b j kept args

def inl {B' : Type} (l' : B' → Label S) {Δ : List Ty} :
    Target S l Qs Δ → Target S (Sum.elim l l') Qs Δ
  | .undefined => .undefined
  | .exit out => .exit out
  | .enter b j kept args => .enter (.inl b) j kept args

def inr {B' : Type} (l' : B' → Label S) {Δ : List Ty} :
    Target S l Qs Δ → Target S (Sum.elim l' l) Qs Δ
  | .undefined => .undefined
  | .exit out => .exit out
  | .enter b j kept args => .enter (.inr b) j kept args

def inj {ι : Type} {F : ι → Type} (l : (i : ι) → F i → Label S) (i : ι) {Δ : List Ty} :
    Target S (l i) Qs Δ → Target S (fun p : (i : ι) × F i => l p.1 p.2) Qs Δ
  | .undefined => .undefined
  | .exit out => .exit out
  | .enter b j kept args => .enter ⟨i, b⟩ j kept args

/-- The action of a bypass case on a target of a diagram with one boundary: the box keeps the
case and its ports, and an exit has the given target. -/
def whisker {M K : Boundary Ty} {B' : Type} (l' : B' → Label S) {Δ : List Ty}
    (m : M.Case) (κ : PortMap Δ m.1)
    (onExit : K.At (Port Δ) → Target S (Sum.elim (fun b => (l b).whisker M) l') Qs Δ) :
    Target S l [K] Δ → Target S (Sum.elim (fun b => (l b).whisker M) l') Qs Δ
  | .undefined => .undefined
  | .exit out => Exits.At.only (X := Port Δ) onExit out
  | .enter b j kept args => .enter (.inl b) (m, j) (kept.append κ) args

/-- The iteration of `Poly_*` on a finite boundary: an exit to the first boundary goes to the
entrance of its case again. The number is the bound on the hops without a box. -/
def iter {K : Boundary Ty} (enter : (c : K.Case) → Target S l (K :: Qs) c.1) :
    Nat → {Δ : List Ty} → Target S l (K :: Qs) Δ → Target S l Qs Δ
  | _, _, .undefined => .undefined
  | _, _, .enter b j kept args => .enter b j kept args
  | 0, Δ, .exit out =>
      Exits.At.elim (X := Port Δ) (fun _ => .undefined) (fun q => .exit q) out
  | n + 1, Δ, .exit out =>
      Exits.At.elim (X := Port Δ) (fun k => (iter enter n (enter k.1)).rename k.2)
        (fun q => .exit q) out

/-- A box with the values of a case of its bypass and of its operands. -/
def Config (S : Signature Ty) {B : Type} (l : B → Label S) (X : Ty → Type) : Type :=
  (b : B) × (((j : (l b).Case) × All X ((l b).ports j)) × All X (S.input (l b).op))

/-- The value of a target at the values of its context. -/
def eval {X : Ty → Type} {Δ : List Ty} : Target S l Qs Δ → All X Δ →
    Option (Qs.At X ⊕ Config S l X)
  | .undefined, _ => none
  | .exit out, env => some (.inl (out.select env))
  | .enter b j kept args, env => some (.inr ⟨b, ⟨j, env.select kept⟩, env.select args⟩)

def withRuntime {X : Ty → Type} {R : Type} (s : R) :
    Qs.At X ⊕ Config S l X → (Qs.At X × R) ⊕ (Config S l X × R)
  | .inl q => .inl (q, s)
  | .inr c => .inr (c, s)

end Target

/-- A wiring from a context: the boxes, the target of the entrance, and the target of each
output case of each box, for each case of its bypass. -/
structure Wired (S : Signature Ty) (Γ : List Ty) (Qs : Exits Ty) where
  Box : Type
  label : Box → Label S
  next : (b : Box) → (j : (label b).Case) → (c : (S.output (label b).op).Case) →
    Target S label Qs (c.1 ++ (label b).ports j)
  root : Target S label Qs Γ

/-- A wiring from a boundary. -/
structure Wiring (S : Signature Ty) (P : Boundary Ty) (Qs : Exits Ty) where
  Box : Type
  label : Box → Label S
  next : (b : Box) → (j : (label b).Case) → (c : (S.output (label b).op).Case) →
    Target S label Qs (c.1 ++ (label b).ports j)
  enter : (c : P.Case) → Target S label Qs c.1

variable {S : Signature Ty}

def Wired.exit {Γ : List Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ)) : Wired S Γ Qs where
  Box := Empty
  label := fun b => nomatch b
  next := fun b => nomatch b
  root := .exit out

def Wired.step {Γ : List Ty} {Qs : Exits Ty} (call : (S.interface (Port Γ)).Shape)
    (rest : (c : (S.output call.1).Case) → Wired S (c.1 ++ Γ) Qs) : Wired S Γ Qs where
  Box := Unit ⊕ ((c : (S.output call.1).Case) × (rest c).Box)
  label := Sum.elim (fun _ => Label.step S call.1 Γ) (fun p => (rest p.1).label p.2)
  next
    | .inl _, _, c =>
        Target.inr (fun _ => Label.step S call.1 Γ)
          (Target.inj (fun c => (rest c).label) c (rest c).root)
    | .inr p, j, c =>
        Target.inr (fun _ => Label.step S call.1 Γ)
          (Target.inj (fun c => (rest c).label) p.1 ((rest p.1).next p.2 j c))
  root := .enter (.inl ()) () (PortMap.id Γ) call.2

def Wired.seq {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (first : Wired S Γ (K :: Qs))
    (next : Wiring S K Qs) : Wired S Γ Qs where
  Box := first.Box ⊕ next.Box
  label := Sum.elim first.label next.label
  next
    | .inl b, j, c =>
        (Target.inl next.label (first.next b j c)).bindHead
          (fun k => Target.inr first.label (next.enter k))
    | .inr b, j, c => Target.inr first.label (next.next b j c)
  root :=
    (Target.inl next.label first.root).bindHead (fun k => Target.inr first.label (next.enter k))

def Wiring.copair {K : Boundary Ty} {Qs : Exits Ty} (each : (c : K.Case) → Wired S c.1 Qs) :
    Wiring S K Qs where
  Box := (c : K.Case) × (each c).Box
  label := fun p => (each p.1).label p.2
  next := fun p j c => Target.inj (fun c => (each c).label) p.1 ((each p.1).next p.2 j c)
  enter := fun c => Target.inj (fun c => (each c).label) c (each c).root

def Wiring.frame {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Wired S Δ [K]) (next : Wiring S (M.product K) Qs) : Wiring S P Qs where
  Box := shared.Box ⊕ next.Box
  label := Sum.elim (fun b => (shared.label b).whisker M) next.label
  next
    | .inl b, (m, j), c =>
        let κ : PortMap (c.1 ++ ((shared.label b).ports j ++ m.1)) m.1 :=
          All.tabulate m.1 (fun _ i => (i.right ((shared.label b).ports j)).right c.1)
        let ρ : PortMap (c.1 ++ ((shared.label b).ports j ++ m.1))
            (c.1 ++ (shared.label b).ports j) :=
          (All.tabulate c.1 (fun _ i => i.left)).append
            (All.tabulate ((shared.label b).ports j) (fun _ i => i.left.right c.1))
        Target.whisker next.label m κ
          (fun k => Target.inr _
            ((next.enter (Boundary.pair m k.1)).rename (k.2.append κ)))
          ((shared.next b j c).rename ρ)
    | .inr b, j, c => Target.inr _ (next.next b j c)
  enter := fun c =>
    Target.whisker next.label (kept c).1 (kept c).2
      (fun k => Target.inr _
        ((next.enter (Boundary.pair (kept c).1 k.1)).rename (k.2.append (kept c).2)))
      (shared.root.rename (args c))

def Wiring.loop {K : Boundary Ty} {Qs : Exits Ty} (body : Wiring S K (K :: Qs)) :
    Wiring S K Qs where
  Box := body.Box
  label := body.label
  next := fun b j c => Target.iter body.enter K.length (body.next b j c)
  enter := fun c => Target.iter body.enter K.length (body.enter c)

mutual

/-- The wiring of a diagram: a recursion on the diagram, with one operation for each form. -/
def Diagram.wired : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Wired S Γ Qs
  | _, _, .exit out => Wired.exit out
  | _, _, .step call rest => Wired.step call fun c => (rest c).wired
  | _, _, .seq first next => Wired.seq first.wired next.wiring

def Continuation.wiring : {P : Boundary Ty} → {Qs : Exits Ty} → Continuation S P Qs →
    Wiring S P Qs
  | _, _, .copair each => Wiring.copair fun c => (each c).wired
  | _, _, .frame kept args shared next => Wiring.frame kept args shared.wired next.wiring
  | _, _, .loop body => Wiring.loop body.wiring

end

/-! The runs of a wiring: one step for each box on the path. -/

section Runs

variable {X : Ty → Type} {R : Type} {Qs : Exits Ty}

/-- One step of a run: the call of the box, and the value of the target of the response. -/
def Target.Step {B : Type} {l : B → Label S}
    (next : (b : B) → (j : (l b).Case) → (c : (S.output (l b).op).Case) →
      Target S l Qs (c.1 ++ (l b).ports j))
    (T : Signature.Calls.{0, 0} S X R) :
    Rel.{0, 0, 0} (Target.Config S l X × R) ((Qs.At X × R) ⊕ (Target.Config S l X × R)) :=
  fun a y =>
    (x : (S.output (l a.1.1).op).At X × R) ×
      (T ⟨(l a.1.1).op, a.1.2.2⟩ a.2 x.1 x.2 ×
        (((next a.1.1 a.1.2.1.1 x.1.1).eval (x.1.2.append a.1.2.1.2)).map
          (Target.withRuntime x.2) ≡ some y))

/-- The runs from the value of a target: an exit, or the loop of the steps from a box. -/
def Target.From {B : Type} {l : B → Label S}
    (next : (b : B) → (j : (l b).Case) → (c : (S.output (l b).op).Case) →
      Target S l Qs (c.1 ++ (l b).ports j))
    (T : Signature.Calls.{0, 0} S X R) :
    Option ((Qs.At X × R) ⊕ (Target.Config S l X × R)) → Qs.At X × R → Type
  | none, _ => Empty
  | some (.inl q), b => q ≡ b
  | some (.inr c), b => Loop (Target.Step next T) c b

/-- The run family of a wiring from a context. -/
def Wired.Runs {Γ : List Ty} (w : Wired S Γ Qs) (T : Signature.Calls.{0, 0} S X R) :
    Rel.{0, 0, 0} (All X Γ × R) (Qs.At X × R) := fun a b =>
  Target.From w.next T ((w.root.eval a.1).map (Target.withRuntime a.2)) b

end Runs

/-! General laws by computation. -/

/-- The first exit equation is an identity of targets: the root of an exit and then a
continuation is the entrance of the continuation at the case of the exit. -/
def Wired.exitSeqRoot {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : K.At (Port Γ))
    (next : Wiring S K Qs) :
    (Wired.seq (Wired.exit (Exits.At.here out)) next).root ≡
      (Target.inr _ (next.enter out.1)).rename out.2 :=
  .refl

/-- The second exit equation: an exit past a continuation is that exit. -/
def Wired.exitPastRoot {Γ : List Ty} {K : Boundary Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ))
    (next : Wiring S K Qs) :
    (Wired.seq (Wired.exit (out.there K)) next).root ≡ .exit out :=
  .refl

end Draft

/-! Checks on the countdown loop. -/

namespace Draft.Checks.Countdown

open Draft

abbrev W : Wired sig [(), ()] [Out] := countdown.wired

def isZeroBox : W.Box := .inr ⟨Boundary.only _, .inl ()⟩

def predBox : W.Box := .inr ⟨Boundary.only _, .inr ⟨⟨_, .there .here⟩, .inl ()⟩⟩

def emitBox : W.Box :=
  .inr ⟨Boundary.only _, .inr ⟨⟨_, .there .here⟩, .inr ⟨Boundary.only _, .inl ()⟩⟩⟩

set_option smartUnfolding false in
/-- The entrance goes to the test, with the two inputs. -/
def rootWire : W.root ≡
    .enter isZeroBox () (.cons .here (.cons (.there .here) .nil)) (.cons .here .nil) := .refl

set_option smartUnfolding false in
/-- The first case of the test goes to the exit, with the value. -/
def exitWire : W.next isZeroBox () ⟨_, .here⟩ ≡
    .exit ⟨_, .here, Boundary.only _, .cons (.there .here) .nil⟩ := .refl

set_option smartUnfolding false in
/-- The second case of the test goes to the predecessor. -/
def predWire : W.next isZeroBox () ⟨_, .there .here⟩ ≡
    .enter predBox () (.cons .here (.cons (.there .here) .nil)) (.cons .here .nil) := .refl

set_option smartUnfolding false in
/-- The feedback wire: the output of the effectful step goes to the input of the test, with
the predecessor and the response. -/
def feedbackWire : W.next emitBox () (Boundary.only _) ≡
    .enter isZeroBox () (.cons (.there .here) (.cons .here .nil))
      (.cons (.there .here) .nil) := .refl

set_option smartUnfolding false in
/-- A run of the wiring from the counter 2, for an arbitrary value and an arbitrary runtime:
seven boxes on the path. -/
def wiredFromTwo (a s : Nat) :
    W.Runs calls (inputs 2 a, s) (out ((s + 1) + (s + a)), s + 2) :=
  Loop.next ⟨(⟨⟨_, .there .here⟩, .nil⟩, s), .refl, .refl⟩
    (Loop.next ⟨(value 1, s), .refl, .refl⟩
      (Loop.next ⟨(value (s + a), s + 1), .refl, .refl⟩
        (Loop.next ⟨(⟨⟨_, .there .here⟩, .nil⟩, s + 1), .refl, .refl⟩
          (Loop.next ⟨(value 0, s + 1), .refl, .refl⟩
            (Loop.next ⟨(value ((s + 1) + (s + a)), s + 2), .refl, .refl⟩
              (Loop.exit ⟨(⟨⟨_, .here⟩, .nil⟩, s + 2), .refl, .refl⟩))))))

set_option smartUnfolding false in
def wiredLength (a s : Nat) : (wiredFromTwo a s).length ≡ 7 := .refl

/-- A loop whose body exits to its entrance with no step. -/
def spin : Continuation sig Entry [Out] :=
  .loop (.one (.exit (Exits.At.here ⟨Boundary.only _, PortMap.id _⟩)))

set_option smartUnfolding false in
/-- The closed silent cycle has the undefined alternative. -/
def spinUndefined : spin.wiring.enter (Boundary.only _) ≡ .undefined := .refl

/-- Two cases. The first exits to the second with the two ports in the other order, and the
second exits from the loop with its first port. -/
def hop : Continuation sig [[(), ()], [(), ()]] [Out] :=
  .loop (.copair fun
    | ⟨_, .here⟩ =>
        .exit (Exits.At.here ⟨⟨_, .there .here⟩, .cons (.there .here) (.cons .here .nil)⟩)
    | ⟨_, .there .here⟩ =>
        .exit ⟨_, .there .here, Boundary.only _, .cons .here .nil⟩)

set_option smartUnfolding false in
/-- The silent path has one exit, and the port maps compose. -/
def hopExit : hop.wiring.enter ⟨_, .here⟩ ≡
    .exit ⟨_, .here, Boundary.only _, .cons (.there .here) .nil⟩ := .refl

end Draft.Checks.Countdown

/-! Checks on the frame. -/

namespace Draft.Checks.Diagram

open Draft

abbrev F : Wired sig [(), ()] [.one [(), ()]] := framed.wired

def testBox : F.Box := .inl (.inl ())

def sharedBox : F.Box := .inr (.inl (.inl ()))

def afterFirstBox : F.Box := .inr (.inr ⟨⟨_, .here⟩, Sum.inl ()⟩)

def afterSecondBox : F.Box := .inr (.inr ⟨⟨_, .there .here⟩, Sum.inl ()⟩)

set_option smartUnfolding false in
/-- The two cases of the test go to the one shared box, each with its case of the bypass. -/
def joinFirst (x y : Nat) :
    (F.next testBox () ⟨_, .here⟩).eval (X := Value) (inputs x y) ≡
      some (.inr ⟨sharedBox, ⟨((⟨_, .here⟩ : bypass.Case), ()), .cons x (.cons y .nil)⟩,
        .cons x .nil⟩) := .refl

set_option smartUnfolding false in
def joinSecond (x y : Nat) :
    (F.next testBox () ⟨_, .there .here⟩).eval (X := Value) (inputs x y) ≡
      some (.inr ⟨sharedBox, ⟨((⟨_, .there .here⟩ : bypass.Case), ()), .cons x (.cons y .nil)⟩,
        .cons x .nil⟩) := .refl

set_option smartUnfolding false in
/-- After the shared box, the case of the bypass gives the continuation, and the kept value
is there with the response. -/
def afterFirst (r x y : Nat) :
    (F.next sharedBox ((⟨_, .here⟩ : bypass.Case), ()) (Boundary.only _)).eval (X := Value)
        (.cons r (.cons x (.cons y .nil))) ≡
      some (.inr ⟨afterFirstBox, ⟨(), .cons r (.cons y .nil)⟩,
        .cons r (.cons y .nil)⟩) := .refl

set_option smartUnfolding false in
def afterSecond (r x y : Nat) :
    (F.next sharedBox ((⟨_, .there .here⟩ : bypass.Case), ()) (Boundary.only _)).eval
        (X := Value) (.cons r (.cons x (.cons y .nil))) ≡
      some (.inr ⟨afterSecondBox, ⟨(), .cons r (.cons y .nil)⟩,
        .cons y (.cons y .nil)⟩) := .refl

end Draft.Checks.Diagram

/-! The loop of a loop has the wires of the loop. -/

namespace Draft.Checks.Countdown

open Draft

/-- The inner loop has the body with its exits under one more boundary, so it has no exit to
its own entrance. The outer loop has the feedback. -/
def nestedLoop : Continuation sig Entry [Out] :=
  .loop (.loop (Continuation.mapExit (Exits.Map.there Entry [Entry, Out]) body))

def nestedTest : nestedLoop.wiring.Box := ⟨Boundary.only _, .inl ()⟩

def nestedEmit : nestedLoop.wiring.Box :=
  ⟨Boundary.only _, .inr ⟨⟨_, .there .here⟩, .inr ⟨Boundary.only _, .inl ()⟩⟩⟩

def loopTest : loop.wiring.Box := ⟨Boundary.only _, .inl ()⟩

def loopEmit : loop.wiring.Box :=
  ⟨Boundary.only _, .inr ⟨⟨_, .there .here⟩, .inr ⟨Boundary.only _, .inl ()⟩⟩⟩

set_option smartUnfolding false in
def loopFeedback : loop.wiring.next loopEmit () (Boundary.only _) ≡
    .enter loopTest () (.cons (.there .here) (.cons .here .nil))
      (.cons (.there .here) .nil) := .refl

set_option smartUnfolding false in
def nestedFeedback : nestedLoop.wiring.next nestedEmit () (Boundary.only _) ≡
    .enter nestedTest () (.cons (.there .here) (.cons .here .nil))
      (.cons (.there .here) .nil) := .refl

set_option smartUnfolding false in
def nestedExit : nestedLoop.wiring.next nestedTest () ⟨_, .here⟩ ≡
    .exit ⟨_, .here, Boundary.only _, .cons (.there .here) .nil⟩ := .refl

end Draft.Checks.Countdown

#print axioms Draft.Diagram.wired
#print axioms Draft.Continuation.wiring
#print axioms Draft.Wired.Runs
#print axioms Draft.Checks.Countdown.wiredFromTwo
#print axioms Draft.Checks.Countdown.hopExit
#print axioms Draft.Checks.Countdown.nestedFeedback
#print axioms Draft.Checks.Diagram.afterSecond
#print axioms Draft.Wired.exitSeqRoot

/-! The wiring as a dependent polynomial on the container of its boxes. -/

namespace Draft

open Prelude Container

variable {Ty : Type} {S : Signature Ty}

/-- The container of the operations: an operation, and an output case. -/
def Signature.cases (S : Signature Ty) : Container := ⟨S.Op, fun o => (S.output o).Case⟩

/-- The container of the boxes: a box, and an output case of its operation. -/
def Wired.boxes {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) : Container :=
  ⟨w.Box, fun b => (S.output (w.label b).op).Case⟩

/-- The boxes are over the operations: the map is the identity on the output cases. -/
def Wired.toCases {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) : Hom w.boxes S.cases where
  shape b := (w.label b).op
  position _ c := c

/-- The precondition is a case of the bypass. The postcondition of an output case is the type
of the targets from the ports of that case and of the bypass case. -/
def Wired.spec {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) : DepPoly w.boxes where
  Pre b := (w.label b).Case
  Post b j c := Target S w.label Qs (c.1 ++ (w.label b).ports j)

/-- The routes are a dependent function of that specification, by definition. -/
def Wired.routes {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) :
    (b : w.boxes.Shape) → (j : w.spec.Pre b) → (c : w.boxes.Pos b) → w.spec.Post b j c :=
  w.next

/-- With a choice of an output case for each box, the routes are evidence in the sense of
`Prelude`. -/
def Wired.evidence {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) (choice : Section w.boxes) :
    Evidence w.spec choice :=
  fun b j => w.next b j (choice b)

def Wiring.boxes {P : Boundary Ty} {Qs : Exits Ty} (w : Wiring S P Qs) : Container :=
  ⟨w.Box, fun b => (S.output (w.label b).op).Case⟩

/-- The boxes of a copairing are the family sum of `Prelude`, and its bypass cases are the
precondition of `DepPoly.sigma`. -/
def copairBoxes {K : Boundary Ty} {Qs : Exits Ty} (each : (c : K.Case) → Wired S c.1 Qs) :
    (Wiring.copair each).boxes ≡ Container.sigma (fun c => (each c).boxes) := .refl

def copairPre {K : Boundary Ty} {Qs : Exits Ty} (each : (c : K.Case) → Wired S c.1 Qs)
    (b : (c : K.Case) × (each c).Box) :
    ((Wiring.copair each).label b).Case ≡ (DepPoly.sigma (fun c => (each c).spec)).Pre b :=
  .refl

/-- The state of the machine: a box with a case of its bypass. This is the shape of the
polynomial `Σ b, m b` of the source. -/
def Wired.State {Γ : List Ty} {Qs : Exits Ty} (w : Wired S Γ Qs) : Type :=
  (b : w.boxes.Shape) × w.spec.Pre b

end Draft
