import Draft.Source

/-! Orders of the steps of a diagram.

A step is ready in a diagram when it can move to the front. Its operands are ports of the
context of the diagram, so no operand is an output of a step before it. Each step before it is
pure, or the step is pure. The evidence follows the path to the step. The step is the first
step, or it is ready in the rest of the first step at each output case of that step, with
operands that are ports of the context before that step. The evidence has the diagram after the
step: each step that the ready step passes has the same operands, and the rest has the output
ports in the other order.

One theorem gives the derivation from a diagram to the diagram with a ready step at the front,
in each rule set that has the interchange rule. The derivation has one interchange for each
step that the ready step passes.

An order of a diagram is a diagram with the evidence that it is an order. The diagram is the
plain part, and the evidence follows its constructors. An exit is the source diagram. A step
has the evidence that it is ready in the source diagram, which is the witness of a
precondition, and the diagram of each output case has the evidence for the diagram after the
step. The derivation from the source diagram to an order has one application of the theorem
for each step.

For a diagram of the fragment with fixed occurrences, the ready steps are a list. A step of the
rest of the first step is ready in the diagram when one of the two steps is pure and its
operands have no output port of the first step. The orders of the diagram are a list too: one
order for each choice of a ready step at each point. The diagram after a ready step and each
order are diagrams of the fragment.

A move of a ready step keeps each occurrence of the dependency graph. The occurrences of the
diagram have the occurrence of the ready step at the number of the steps that it passes, and
the other occurrences are the occurrences of the diagram after the step. The word of an order
has that number for each of its steps. It is an admissible order of the occurrences of the
source diagram: the evidence of the specification of the runs follows the steps of the order,
with the theorem of the move as the witness of each precondition.

The other direction holds for a diagram of the fragment whose occurrences have no element at
two positions. The step of an admitted run is a ready step: no operand of it is an output port
of a step before it, because the call of that step is not done, and one of each two steps is
pure, because the effectful call before the step is done. An admissible order of the
occurrences is thus the word of an order: the order has the ready step of each run.

A derivation of the interchange equation set keeps the fragment and the occurrences: the two
diagrams have the same occurrences, each the same number of times. The statement is a
correspondence of the positions of each occurrence in the two lists, with the two round trips.
The interchange rule gives the first two occurrences in the other order, an agreement gives the
same occurrences, and the correspondence has the symmetry, the composition, and the congruence
of a derivation.

The list of the orders of a diagram of the fragment is complete: each order of the diagram
agrees with an order of the list. The evidence of an order has functions of the output cases,
and the list has the functions that the value at the center of the cases gives, so the
statement is an agreement of diagrams. Each ready step is in the list of the ready steps, with
a diagram after it that agrees at each case: the decision of the kinds has a value, and the
operands are weakened operands. The proof is for each diagram that agrees with the source
diagram, so the diagram after a ready step of the list takes the place of the diagram after
the given ready step. The bound of the list is the number of the steps, and the diagram after
a ready step has one step less.

A test with two cases has a list of ready steps, when the rest of each case is a diagram of
the fragment. The list has the test, and each step that is ready in the rest of the two cases
with one operation and the same operands. The operands are ports of the context of the test,
and the test is pure or the step is pure. A ready step of the first case and a ready step of
the second case give one element of the list. The list is complete for the moves before the
test: each step that is ready in the rest of each case, with operands of the context of the
test, is in the list, with a diagram after it that agrees at each case. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty}

/-- The step of the operation `b` with the operands `args` is ready in a diagram, and `after`
is the diagram after it. -/
inductive Diagram.Ready (b : S.Op) : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs →
    PortMap Γ (S.input b) → ((cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs) → Type where
  /-- The first step is ready. -/
  | here {Γ : List Ty} {Qs : Exits Ty} (args : PortMap Γ (S.input b))
      (rest : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs) :
      Diagram.Ready b (.step ⟨b, args⟩ rest) args rest
  /-- A step that is ready in the rest of the first step at each output case, with operands of
  the context before the first step, is ready when one of the two steps is pure. -/
  | past {Γ : List Ty} {Qs : Exits Ty} (a : S.Op)
      (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
      (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
      {rest : (ca : (S.output a).Case) → Diagram S (ca.1 ++ Γ) Qs}
      {after : (ca : (S.output a).Case) → (cb : (S.output b).Case) →
        Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs}
      (inner : (ca : (S.output a).Case) →
        Diagram.Ready b (rest ca) (second.weaken ca.1) (after ca)) :
      Diagram.Ready b (.step ⟨a, first⟩ rest) second
        (fun cb => .step ⟨a, first.weaken cb.1⟩ fun ca =>
          Diagram.rename (PortMap.exchange ca.1 cb.1 Γ) (after ca cb))

/-- A ready step moves to the front: the derivation from the diagram to the step and then the
diagram after it. It has one interchange for each step that the ready step passes. -/
def Diagram.Ready.derivation {R : Rules S} (inter : Rules.Map (Rules.interchange S) R)
    {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) : Diagram.Derivation R d (.step ⟨b, args⟩ after) :=
  Diagram.Ready.casesOn
    (motive := @fun _ _ d args after _ => Diagram.Derivation R d (.step ⟨b, args⟩ after)) r
    (fun args rest => .agree (.refl (.step ⟨b, args⟩ rest)))
    (@fun _ _ a central first second _ after inner =>
      .trans (.step ⟨a, first⟩ fun ca => (inner ca).derivation inter)
        (.rule (inter.diagram (.swap a b central first second after))))

/-- A step is ready past a first step whose output boundary has one case: the type of the
cases is contractible. The evidence in the rest at the center gives the evidence at each
case. -/
def Diagram.Ready.pastOne {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} (a : S.Op)
    (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
    {rest : (ca : (S.output a).Case) → Diagram S (ca.1 ++ Γ) Qs}
    (one : IsContr (S.output a).Case)
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (one.1.1 ++ Γ)) Qs}
    (inner : Diagram.Ready b (rest one.1) (second.weaken one.1.1) after) :
    (afterEach : (ca : (S.output a).Case) → (cb : (S.output b).Case) →
        Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs) ×
      Diagram.Ready b (.step ⟨a, first⟩ rest) second
        (fun cb => .step ⟨a, first.weaken cb.1⟩ fun ca =>
          Diagram.rename (PortMap.exchange ca.1 cb.1 Γ) (afterEach ca cb)) :=
  let spread (ca : (S.output a).Case) :
      (aft : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs) ×
        Diagram.Ready b (rest ca) (second.weaken ca.1) aft :=
    Identity.transport
      (fun (c : (S.output a).Case) =>
        (aft : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) ×
          Diagram.Ready b (rest c) (second.weaken c.1) aft)
      (one.2 ca) ⟨after, inner⟩
  ⟨fun ca => (spread ca).1, .past a central first second fun ca => (spread ca).2⟩

/-- The evidence that the diagram `e` is an order of the diagram `d`, by the constructors of
`e`. An exit is the diagram `d`. A step has the diagram after it and the evidence that it is
ready in `d`, and the diagram of each output case has the evidence for the diagram after the
step at that case. -/
def Diagram.Order : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) → Type
  | _, _, .exit out, d => Diagram.exit out ≡ d
  | Γ, Qs, .step call rest, d =>
      (after : (cb : (S.output call.1).Case) → Diagram S (cb.1 ++ Γ) Qs) ×
        (Diagram.Ready call.1 d call.2 after ×
          ((cb : (S.output call.1).Case) → Diagram.Order (rest cb) (after cb)))
  | _, _, .seq _ _, _ => Empty

/-- The derivation from a diagram to an order of it, in each rule set that has the interchange
rule: one move of a ready step for each step of the order. -/
def Diagram.Order.derivation {R : Rules S} (inter : Rules.Map (Rules.interchange S) R) :
    {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) → Diagram.Order e d →
    Diagram.Derivation R d e
  | _, _, .exit out, _, same =>
      Identity.transport (fun x => Diagram.Derivation R x (.exit out)) same
        (.agree (.refl (.exit out)))
  | _, _, .step call rest, _, o =>
      .trans (o.2.1.derivation inter)
        (.step call fun cb => Diagram.Order.derivation inter (rest cb) (o.1 cb) (o.2.2 cb))
  | _, _, .seq _ _, _, o => nomatch o

/-- The output boundary of a ready step of a diagram of the fragment has one case. -/
def Diagram.Ready.single {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) :
    d.Straight → IsContr (S.output b).Case :=
  Diagram.Ready.casesOn
    (motive := @fun _ _ d _ _ _ =>
      d.Straight → IsContr (S.output b).Case)
    r
    (fun _ _ h => h.1)
    (@fun _ _ _ _ _ _ _ _ inner h => (inner h.1.1).single h.2)

/-- The diagram after a ready step of a diagram of the fragment is a diagram of the fragment,
at each output case of the step. -/
def Diagram.Ready.straight {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) :
    d.Straight → (cb : (S.output b).Case) → (after cb).Straight :=
  Diagram.Ready.casesOn
    (motive := @fun _ _ d _ after _ =>
      d.Straight → (cb : (S.output b).Case) → (after cb).Straight)
    r
    (fun _ rest h cb => Identity.transport (fun c => (rest c).Straight) (h.1.2 cb) h.2)
    (@fun Γ _ _ _ _ _ _ after inner h cb =>
      ⟨h.1,
        Diagram.Straight.rename (PortMap.exchange h.1.1.1 cb.1 Γ) (after h.1.1 cb)
          ((inner h.1.1).straight h.2 cb)⟩)

/-- An order of a diagram of the fragment is a diagram of the fragment. -/
def Diagram.Order.straight : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) →
    Diagram.Order e d → d.Straight → e.Straight
  | _, _, .exit _, _, _, _ => ()
  | _, _, .step _ rest, _, o, h =>
      ⟨o.2.1.single h,
        Diagram.Order.straight (rest (o.2.1.single h).1) (o.1 (o.2.1.single h).1)
          (o.2.2 (o.2.1.single h).1) (o.2.1.straight h (o.2.1.single h).1)⟩
  | _, _, .seq _ _, _, o, _ => nomatch o

/-- The evidence that a call is a ready step of a diagram: the diagram after the step, and the
evidence that the step is ready. -/
abbrev Diagram.ReadyFor {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (call : (S.interface (Port Γ)).Shape) : Type :=
  (after : (cb : (S.output call.1).Case) → Diagram S (cb.1 ++ Γ) Qs) ×
    Diagram.Ready call.1 d call.2 after

/-- A ready step of a diagram: its operation, its operands, the diagram after it, and the
evidence. -/
abbrev Diagram.Choice {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) : Type :=
  (b : S.Op) × ((args : PortMap Γ (S.input b)) ×
    d.ReadyFor ⟨b, args⟩)

/-- The ready step of the diagram from a ready step of the rest of the first step, for a value
of the decision of the kinds and a value of the decision of the operands. -/
def Diagram.Choice.pastOf {Γ : List Ty} {Qs : Exits Ty} (a : S.Op) (first : PortMap Γ (S.input a))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs)
    (one : IsContr (S.output a).Case) (b : S.Op)
    (args : PortMap (one.1.1 ++ Γ) (S.input b))
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (one.1.1 ++ Γ)) Qs}
    (r : Diagram.Ready b (rest one.1) args after)
    (v : Option ((S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure)))
    (w : Option ((inner : PortMap Γ (S.input b)) × (args ≡ inner.weaken one.1.1))) :
    Option (Diagram.step ⟨a, first⟩ rest).Choice :=
  v.bind fun central =>
    w.map fun outer =>
      ⟨b, outer.1, _,
        (Diagram.Ready.pastOne a central first outer.1 one
          (Identity.transport (fun x => Diagram.Ready b (rest one.1) x after) outer.2 r)).2⟩

/-- A ready step of the rest of a first step is a ready step of the diagram when one of the
two steps is pure, and its operands have no output port of the first step. The output boundary
of the first step has one case. -/
def Diagram.Choice.past {Γ : List Ty} {Qs : Exits Ty} (a : S.Op) (first : PortMap Γ (S.input a))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs)
    (one : IsContr (S.output a).Case) (choice : (rest one.1).Choice) :
    Option (Diagram.step ⟨a, first⟩ rest).Choice :=
  Diagram.Choice.pastOf a first rest one choice.1 choice.2.1 choice.2.2.2
    (Kind.central (S.kind a) (S.kind choice.1)) (PortMap.strengthen one.1.1 choice.2.1)

/-- The ready steps of a diagram of the fragment, in the order of its steps. The first step is
ready. A ready step of its rest is ready when one of the two steps is pure, and its operands
have no output port of the first step. -/
def Diagram.choices : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    List d.Choice
  | _, _, .exit _, _ => []
  | _, _, .step ⟨a, first⟩ rest, h =>
      ⟨a, first, rest, .here first rest⟩ ::
        (Diagram.choices (rest h.1.1) h.2).filterMap (Diagram.Choice.past a first rest h.1)
  | _, _, .seq _ _, _ => []

/-- A ready step as the ready step of a call. The decision of the identity of the two calls
gives the evidence for the call when the operation and the operands are the same, and no
value when they are not. -/
def Diagram.Choice.atCall [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    (k : d.Choice) (call : (S.interface (Port Γ)).Shape) : Option (d.ReadyFor call) :=
  Dec.transport? d.ReadyFor k.2.2 (Dec.sigma (P := fun b => PortMap Γ (S.input b)) decideEq
    (fun _ => All.decide (fun _ => Elem.decide)) ⟨k.1, k.2.1⟩ call)

section Binary

variable {Γ : List Ty} {Qs : Exits Ty} (a : S.Op) (first : PortMap Γ (S.input a))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs)
    (two : (S.output a).Binary)

/-- A step that is ready in the rest of each of the two cases of a test, with operands of the
context of the test, is ready in the diagram of the test. The diagram after it has the test,
and then the diagram after the step in each case, with the output ports in the other order. -/
def Diagram.Ready.pastBinary {b : S.Op} (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    (args : PortMap Γ (S.input b))
    (l : (rest two.left).ReadyFor ⟨b, args.weaken two.left.1⟩)
    (r : (rest two.right).ReadyFor ⟨b, args.weaken two.right.1⟩) :
    (Diagram.step ⟨a, first⟩ rest).ReadyFor ⟨b, args⟩ :=
  let each := two.elim (F := fun c => (rest c).ReadyFor ⟨b, args.weaken c.1⟩) l r
  ⟨_, .past a central first args fun c => (each c).2⟩

variable [DecEq S.Op]

/-- The ready steps of a test from one ready step of the rest of the first case, for a value
of the decision of the kinds and a value of the decision of the operands: one ready step for
each ready step of the rest of the second case with the same operation and the same operands.
The operands are ports of the context of the test. -/
private def Diagram.Choice.matchRight (l : (rest two.left).Choice)
    (rights : List (rest two.right).Choice)
    (central : Option ((S.kind a ≡ .pure) ⊕ (S.kind l.1 ≡ .pure)))
    (outer : Option ((args : PortMap Γ (S.input l.1)) × (l.2.1 ≡ args.weaken two.left.1))) :
    List (Diagram.step ⟨a, first⟩ rest).Choice :=
  central.elim [] fun ok => outer.elim [] fun inputs =>
    let left := Identity.transport (fun ps => (rest two.left).ReadyFor ⟨l.1, ps⟩) inputs.2 l.2.2
    rights.filterMap fun r => (r.atCall ⟨l.1, inputs.1.weaken two.right.1⟩).map fun right =>
      ⟨l.1, inputs.1, Diagram.Ready.pastBinary a first rest two ok inputs.1 left right⟩

/-- The ready steps of a test with two cases, when the rest of each case is a diagram of the
fragment. The test is ready. A step is ready when it is ready in the rest of the two cases
with one operation and the same operands, its operands are ports of the context of the test,
and the test is pure or the step is pure. A ready step of the first case and a ready step of
the second case give one element, so two equal calls in one case give different elements, each
with its diagram after the step. -/
def Diagram.binaryChoices (arms : (c : (S.output a).Case) → (rest c).Straight) :
    List (Diagram.step ⟨a, first⟩ rest).Choice :=
  let rights := (rest two.right).choices (arms two.right)
  ⟨a, first, rest, .here first rest⟩ :: ((rest two.left).choices (arms two.left)).flatMap fun l =>
    Diagram.Choice.matchRight a first rest two l rights (Kind.central (S.kind a) (S.kind l.1))
      (PortMap.strengthen two.left.1 l.2.1)

end Binary

/-- The order with a ready step first, from an order of the diagram after that step at the
center of the output cases of the step. The order at the center gives the order at each
case. -/
def Diagram.Order.pick {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs} (b : S.Op)
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (ready : Diagram.Ready b d args after) (one : IsContr (S.output b).Case)
    (tail : (e : Diagram S (one.1.1 ++ Γ) Qs) × Diagram.Order e (after one.1)) :
    (e : Diagram S Γ Qs) × Diagram.Order e d :=
  let spread (cb : (S.output b).Case) :
      (e : Diagram S (cb.1 ++ Γ) Qs) × Diagram.Order e (after cb) :=
    Identity.transport
      (fun (c : (S.output b).Case) =>
        (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (after c))
      (one.2 cb) tail
  ⟨.step ⟨b, args⟩ fun cb => (spread cb).1, after, ready, fun cb => (spread cb).2⟩

/-- The orders of a diagram of the fragment that has at most a given number of steps: one
order for each choice of a ready step at each point. -/
def Diagram.ordersWithin : Nat → {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    d.Straight → List ((e : Diagram S Γ Qs) × Diagram.Order e d)
  | 0, _, _, .exit out, _ => [⟨.exit out, .refl⟩]
  | 0, _, _, .step _ _, _ => []
  | 0, _, _, .seq _ _, _ => []
  | _ + 1, _, _, .exit out, _ => [⟨.exit out, .refl⟩]
  | n + 1, _, _, .step call rest, h =>
      (Diagram.choices (.step call rest) h).flatMap fun choice =>
        (Diagram.ordersWithin n (choice.2.2.1 (choice.2.2.2.single h).1)
            (choice.2.2.2.straight h (choice.2.2.2.single h).1)).map fun tail =>
          Diagram.Order.pick choice.1 choice.2.2.2 (choice.2.2.2.single h) tail
  | _ + 1, _, _, .seq _ _, _ => []

/-- The orders of a diagram of the fragment. -/
def Diagram.orders {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight) :
    List ((e : Diagram S Γ Qs) × Diagram.Order e d) :=
  Diagram.ordersWithin (d.ops h).length d h

/-- The number of the steps that a ready step of a diagram of the fragment passes. -/
def Diagram.Ready.depth {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) : d.Straight → Nat :=
  Diagram.Ready.casesOn (motive := @fun _ _ d _ _ _ => d.Straight → Nat) r
    (fun _ _ _ => 0)
    (@fun _ _ _ _ _ _ _ _ inner h => (inner h.1.1).depth h.2 + 1)

/-- The step of a move past one step: the occurrences of the two steps and of the rest do not
change. -/
def Diagram.movedPast {Γ₀ : List Ty} (a b : S.Op)
    (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    {Γ : List Ty} {Qs : Exits Ty} (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
    (ca : (S.output a).Case) (cb : (S.output b).Case)
    (X : Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs) (sX : X.Straight)
    (env : All (History S Γ₀) Γ) (last : Option (Effect S Γ₀))
    (found : Option (S.Occurrence Γ₀ × List (S.Occurrence Γ₀)))
    (inner : found ≡
      some (⟨b, Call.at b (second.weaken ca.1) ((Call.at a first env last).outputs ca env)
            ((Call.at a first env last).next last)⟩,
        X.occurrences sX
          ((Call.at b (second.weaken ca.1) ((Call.at a first env last).outputs ca env)
              ((Call.at a first env last).next last)).outputs cb
            ((Call.at a first env last).outputs ca env))
          ((Call.at b (second.weaken ca.1) ((Call.at a first env last).outputs ca env)
              ((Call.at a first env last).next last)).next
            ((Call.at a first env last).next last)))) :
    found.map (fun f => (f.1, (⟨a, Call.at a first env last⟩ : S.Occurrence Γ₀) :: f.2)) ≡
      some (⟨b, Call.at b second env last⟩,
        (⟨a, Call.at a (first.weaken cb.1) ((Call.at b second env last).outputs cb env)
            ((Call.at b second env last).next last)⟩ : S.Occurrence Γ₀) ::
          (X.rename (PortMap.exchange ca.1 cb.1 Γ)).occurrences
            (Diagram.Straight.rename (PortMap.exchange ca.1 cb.1 Γ) X sX)
            ((Call.at a (first.weaken cb.1) ((Call.at b second env last).outputs cb env)
                ((Call.at b second env last).next last)).outputs ca
              ((Call.at b second env last).outputs cb env))
            ((Call.at a (first.weaken cb.1) ((Call.at b second env last).outputs cb env)
                ((Call.at b second env last).next last)).next
              ((Call.at b second env last).next last))) :=
  let A : Call S Γ₀ a := Call.at a first env last
  let B : Call S Γ₀ b := Call.at b second env last
  let Bi : Call S Γ₀ b := Call.at b (second.weaken ca.1) (A.outputs ca env) (A.next last)
  let A' : Call S Γ₀ a := Call.at a (first.weaken cb.1) (B.outputs cb env) (B.next last)
  let F (x : Call S Γ₀ a) (y : Call S Γ₀ b) (l : Option (Effect S Γ₀)) :
      Option (S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) :=
    some (⟨b, y⟩,
      (⟨a, x⟩ : S.Occurrence Γ₀) :: X.occurrences sX (y.outputs cb (x.outputs ca env)) l)
  let eB : Bi ≡ B :=
    Identity.cong₂
      (fun (x : All (History S Γ₀) (S.input b)) (y : Option (Effect S Γ₀)) => Call.mk x y)
      (PortMap.selectWeaken _ env second)
      (Kind.beforeSecond (S.kind a) (S.kind b) central last (.after A))
  let eA : A' ≡ A :=
    Identity.cong₂
      (fun (x : All (History S Γ₀) (S.input a)) (y : Option (Effect S Γ₀)) => Call.mk x y)
      (PortMap.selectWeaken _ env first)
      (Kind.beforeFirst (S.kind a) (S.kind b) central last (.after B))
  (((Identity.cong
        (Option.map fun (f : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) =>
          (f.1, (⟨a, A⟩ : S.Occurrence Γ₀) :: f.2)) inner :
        found.map (fun f => (f.1, (⟨a, A⟩ : S.Occurrence Γ₀) :: f.2)) ≡
          F A Bi (Bi.next (A.next last)))).trans
      ((Identity.cong (fun y => F A y (y.next (A.next last))) eB).trans
        ((Identity.cong (fun l => F A B l)
            (Kind.lastSwap (S.kind a) (S.kind b) central last (.after A) (.after B))).trans
          (Identity.cong (fun x => F x B (x.next (B.next last))) eA).symm))).trans
    (Identity.cong
        (fun tail => some ((⟨b, B⟩ : S.Occurrence Γ₀), (⟨a, A'⟩ : S.Occurrence Γ₀) :: tail))
        ((Diagram.occurrencesRename (PortMap.exchange ca.1 cb.1 Γ) X sX
            (A'.outputs ca (B.outputs cb env)) (A'.next (B.next last))).trans
          (Identity.cong (fun vals => X.occurrences sX vals (A'.next (B.next last)))
            (PortMap.selectExchange _ _ env)))).symm

/-- A move of a ready step keeps each occurrence. The occurrences of the diagram have the
occurrence of the ready step at the number of the steps that it passes. The other occurrences,
in their order, are the occurrences of the diagram after the step. -/
def Diagram.Ready.moved {Γ₀ : List Ty} {b : S.Op} {Γ : List Ty} {Qs : Exits Ty}
    {d : Diagram S Γ Qs} {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) :
    (h : d.Straight) → (env : All (History S Γ₀) Γ) → (last : Option (Effect S Γ₀)) →
    takeAt (r.depth h) (d.occurrences h env last) ≡
      some (⟨b, Call.at b args env last⟩,
        (after (r.single h).1).occurrences (r.straight h (r.single h).1)
          ((Call.at b args env last).outputs (r.single h).1 env)
          ((Call.at b args env last).next last)) :=
  Diagram.Ready.casesOn
    (motive := @fun Γ _ d args after r =>
      (h : d.Straight) → (env : All (History S Γ₀) Γ) → (last : Option (Effect S Γ₀)) →
      takeAt (r.depth h) (d.occurrences h env last) ≡
        some (⟨b, Call.at b args env last⟩,
          (after (r.single h).1).occurrences (r.straight h (r.single h).1)
            ((Call.at b args env last).outputs (r.single h).1 env)
            ((Call.at b args env last).next last)))
    r
    (fun args rest h env last =>
      Identity.cong
        (fun tail => some ((⟨b, Call.at b args env last⟩ : S.Occurrence Γ₀), tail))
        (Diagram.occurrencesCase rest (h.1.2 h.1.1) h.2 (Call.at b args env last) env
          ((Call.at b args env last).next last)))
    (@fun _ _ a central first second rest after inner h env last =>
      Diagram.movedPast a b central first second h.1.1 ((inner h.1.1).single h.2).1
        (after h.1.1 ((inner h.1.1).single h.2).1)
        ((inner h.1.1).straight h.2 ((inner h.1.1).single h.2).1) env last
        (takeAt ((inner h.1.1).depth h.2)
          ((rest h.1.1).occurrences h.2 ((Call.at a first env last).outputs h.1.1 env)
            ((Call.at a first env last).next last)))
        ((inner h.1.1).moved h.2 ((Call.at a first env last).outputs h.1.1 env)
          ((Call.at a first env last).next last)))

/-! The occurrences along a derivation of the interchange equation set. -/

section Kept

variable {Γ₀ : List Ty}

/-- Two diagrams are in the fragment together, and they have the same occurrences, each the
same number of times, for each evidence of the fragment. -/
abbrev Diagram.Kept (Γ₀ : List Ty) {Γ : List Ty} {Qs : Exits Ty} (d e : Diagram S Γ Qs) : Type :=
  (d.Straight → e.Straight) × ((e.Straight → d.Straight) ×
    ((h : d.Straight) → (h' : e.Straight) → (env : All (History S Γ₀) Γ) →
      (last : Option (Effect S Γ₀)) →
      Elem.Same (d.occurrences h env last) (e.occurrences h' env last)))

namespace Diagram.Kept

variable {Γ₀ : List Ty} {Γ : List Ty} {Qs : Exits Ty}

def symm {d e : Diagram S Γ Qs} (k : Diagram.Kept Γ₀ d e) : Diagram.Kept Γ₀ e d :=
  ⟨k.2.1, k.1, fun h h' env last => (k.2.2 h' h env last).symm⟩

def trans {d m e : Diagram S Γ Qs} (k : Diagram.Kept Γ₀ d m) (l : Diagram.Kept Γ₀ m e) :
    Diagram.Kept Γ₀ d e :=
  ⟨fun h => l.1 (k.1 h), fun h => k.2.1 (l.2.1 h),
    fun h h' env last => (k.2.2 h (k.1 h) env last).trans (l.2.2 (k.1 h) h' env last)⟩

/-- A step with the same call, and a rest that keeps the occurrences at each case. -/
def step (call : (S.interface (Port Γ)).Shape)
    {rest rest' : (c : (S.output call.1).Case) → Diagram S (c.1 ++ Γ) Qs}
    (each : (c : (S.output call.1).Case) → Diagram.Kept Γ₀ (rest c) (rest' c)) :
    Diagram.Kept Γ₀ (.step call rest) (.step call rest') :=
  ⟨fun h => ⟨h.1, (each h.1.1).1 h.2⟩, fun h => ⟨h.1, (each h.1.1).2.1 h.2⟩,
    fun h h' env last =>
      Elem.Same.cons _
        (Identity.ind
          (fun (c : (S.output call.1).Case) (_ : h.1.1 ≡ c) => (t : (rest' c).Straight) →
            Elem.Same
              ((rest h.1.1).occurrences h.2 ((Call.at call.1 call.2 env last).outputs h.1.1 env)
                ((Call.at call.1 call.2 env last).next last))
              ((rest' c).occurrences t ((Call.at call.1 call.2 env last).outputs c env)
                ((Call.at call.1 call.2 env last).next last)))
          (fun t => (each h.1.1).2.2 h.2 t _ _) (h.1.2 h'.1.1) h'.2)⟩

end Diagram.Kept


/-- Two diagrams that agree have the same occurrences. -/
def Diagram.Kept.ofAgreement : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} →
    Diagram.Agreement d e → Diagram.Kept Γ₀ d e
  | _, _, _, _, .exit _ => ⟨fun h => h, fun h => h, fun _ _ _ _ => Elem.Same.refl _⟩
  | _, _, _, _, .step call each => Diagram.Kept.step call fun c => ofAgreement (each c)
  | _, _, _, _, .seq _ _ =>
      ⟨fun h => (nomatch h), fun h => (nomatch h), fun h _ _ _ => (nomatch h)⟩

/-- The interchange rule keeps the occurrences: the two steps have the other order. -/
def Diagram.Kept.ofInterchange {Γ : List Ty} {Qs : Exits Ty} :
    {d e : Diagram S Γ Qs} → Diagram.Interchange d e → Diagram.Kept Γ₀ d e
  | _, _, .swap a b central first second rest =>
      let fwd (h : (Diagram.step ⟨a, first⟩ fun ca =>
          Diagram.step ⟨b, second.weaken _⟩ fun cb => rest ca cb).Straight) :
          (Diagram.step ⟨b, second⟩ fun cb => Diagram.step ⟨a, first.weaken _⟩ fun ca =>
            Diagram.rename (PortMap.exchange _ _ Γ) (rest ca cb)).Straight :=
        ⟨h.2.1, h.1,
          Diagram.Straight.rename (PortMap.exchange _ _ Γ) (rest h.1.1 h.2.1.1) h.2.2⟩
      ⟨fwd,
        fun h => ⟨h.2.1, h.1,
          Diagram.Straight.ofRename (PortMap.exchange _ _ Γ) (rest h.2.1.1 h.1.1) h.2.2⟩,
        fun h h' env last =>
          let moved :=
            Identity.someInject
              (Diagram.movedPast a b central first second h.1.1 h.2.1.1 (rest h.1.1 h.2.1.1)
                h.2.2 env last _ .refl)
          ((Elem.Same.swap _ _ _).trans
              (Elem.Same.ofIdentity
                (Identity.cong
                  (fun (r : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) => r.1 :: r.2) moved))).trans
            ((Diagram.Kept.ofAgreement (Γ₀ := Γ₀) (Diagram.Agreement.refl _)).2.2 (fwd h) h'
              env last)⟩

/-- A derivation of the interchange equation set keeps the fragment and the occurrences, each
the same number of times. -/
def Diagram.Derivation.kept : {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} →
    Diagram.Derivation (Rules.interchange S) d e → Diagram.Kept Γ₀ d e
  | _, _, _, _, .agree a => Diagram.Kept.ofAgreement a
  | _, _, _, _, .rule r => Diagram.Kept.ofInterchange r
  | _, _, _, _, .symm h => (Diagram.Derivation.kept h).symm
  | _, _, _, _, .trans h k => (Diagram.Derivation.kept h).trans (Diagram.Derivation.kept k)
  | _, _, _, _, .step call each => Diagram.Kept.step call fun c => Diagram.Derivation.kept (each c)
  | _, _, _, _, .seq _ _ =>
      ⟨fun h => (nomatch h), fun h => (nomatch h), fun h _ _ _ => (nomatch h)⟩

/-- The graphs of the two diagrams of a derivation of the interchange equation set have the
same occurrences, each the same number of times. -/
def Diagram.Derivation.graphKept {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs}
    (der : Diagram.Derivation (Rules.interchange S) d e) (h : d.Straight) (h' : e.Straight) :
    Elem.Same (d.graph h) (e.graph h') :=
  (Diagram.Derivation.kept (Γ₀ := Γ) der).2.2 h h' (S.inputs Γ) none

end Kept

section Admissible

variable {Γ₀ : List Ty}

/-- A produced history stays produced with one more done occurrence. -/
def History.Produced.weaken {done : List (S.Occurrence Γ₀)} (x : S.Occurrence Γ₀) :
    {t : Ty} → (v : History S Γ₀ t) → History.Produced done v → History.Produced (x :: done) v
  | _, .input _, _ => ()
  | _, .output _ _ _, i => .there i

/-- The same for the effectful call before a call. -/
def Effect.Produced.weaken {done : List (S.Occurrence Γ₀)} (x : S.Occurrence Γ₀) :
    (last : Option (Effect S Γ₀)) → Effect.Produced done last → Effect.Produced (x :: done) last
  | none, _ => ()
  | some (.after _), i => .there i

/-- The effectful call before a step of each kind is done, when the last effectful call is. -/
def Effect.Produced.before {done : List (S.Occurrence Γ₀)} {last : Option (Effect S Γ₀)}
    (h : Effect.Produced done last) : (k : Kind) → Effect.Produced done (Kind.before k last)
  | .pure => ()
  | .effectful => h

/-- The last effectful call after a call is done, with the occurrence of that call. -/
def Effect.Produced.last {done : List (S.Occurrence Γ₀)} {o : S.Op} (call : Call S Γ₀ o)
    {last : Option (Effect S Γ₀)} (h : Effect.Produced done last) :
    (k : Kind) → Effect.Produced (⟨o, call⟩ :: done) (Kind.last k last (.after call))
  | .pure => Effect.Produced.weaken _ last h
  | .effectful => .here

/-- Each history of a context is produced. -/
abbrev Signature.Known (done : List (S.Occurrence Γ₀)) {Γ : List Ty}
    (env : All (History S Γ₀) Γ) : Type :=
  (t : Ty) → (p : Port Γ t) → History.Produced done (env.lookup p)

/-- Each input is produced. -/
def Signature.Known.inputs : Signature.Known ([] : List (S.Occurrence Γ₀)) (S.inputs Γ₀) :=
  fun _ p =>
    Identity.transport (History.Produced []) (All.lookupTabulate (fun _ q => History.input q) p).symm
      ()

/-- After a call, each history of the context is produced: an output port of the call has the
occurrence of the call, and each other history stays produced. -/
def Signature.Known.outputs {done : List (S.Occurrence Γ₀)} {o : S.Op} (call : Call S Γ₀ o)
    (c : (S.output o).Case) {Γ : List Ty} {env : All (History S Γ₀) Γ}
    (known : Signature.Known done env) :
    Signature.Known (⟨o, call⟩ :: done) (call.outputs c env) :=
  fun t p =>
    match Elem.split c.1 p with
    | .inl found =>
        Identity.transport
          (fun q => History.Produced (⟨o, call⟩ :: done) ((call.outputs c env).lookup q))
          found.2.symm
          (Identity.transport (History.Produced (⟨o, call⟩ :: done))
            ((All.lookupLeft _ env found.1).trans
              (All.lookupTabulate (fun _ q => History.output call c q) found.1)).symm
            .here)
    | .inr found =>
        Identity.transport
          (fun q => History.Produced (⟨o, call⟩ :: done) ((call.outputs c env).lookup q))
          found.2.symm
          (Identity.transport (History.Produced (⟨o, call⟩ :: done))
            (All.lookupRight _ env found.1).symm
            (History.Produced.weaken _ _ (known t found.1)))

/-- The word of an order of a diagram of the fragment: for each step of the order, the number
of the steps that its ready step passes. -/
def Diagram.Order.depths : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) →
    Diagram.Order e d → d.Straight → List Nat
  | _, _, .exit _, _, _, _ => []
  | _, _, .step _ rest, _, o, h =>
      o.2.1.depth h ::
        Diagram.Order.depths (rest (o.2.1.single h).1) (o.1 (o.2.1.single h).1)
          (o.2.2 (o.2.1.single h).1) (o.2.1.straight h (o.2.1.single h).1)
  | _, _, .seq _ _, _, o, _ => nomatch o

/-- The word of an order of a diagram of the fragment is an admissible order of the occurrences
of the diagram: the evidence of the specification of the runs, from each list of done
occurrences that has the call of each history of the context and the last effectful call. -/
def Diagram.Order.admissible : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) →
    (o : Diagram.Order e d) → (h : d.Straight) → (env : All (History S Γ₀) Γ) →
    (last : Option (Effect S Γ₀)) → (done : List (S.Occurrence Γ₀)) →
    Signature.Known done env → Effect.Produced done last →
    FreeDep (S.admissible Γ₀) (S.Finished Γ₀)
      ((word (Diagram.Order.depths e d o h)).thread (E := Empty)
        (d.occurrences h env last, done))
  | Γ, Qs, .exit _, d, same, h, env, last, _, _, _ =>
      .pure
        (Identity.ind
          (fun (d : Diagram S Γ Qs) _ =>
            (h : d.Straight) → d.occurrences h env last ≡ ([] : List (S.Occurrence Γ₀)))
          (fun _ => .refl) same h :
          d.occurrences h env last ≡ ([] : List (S.Occurrence Γ₀)))
  | _, _, .step call rest, d, o, h, env, last, done, known, before =>
      Signature.ran (o.2.1.depth h) (d.occurrences h env last, done)
        ⟨(⟨call.1, Call.at call.1 call.2 env last⟩,
            (o.1 (o.2.1.single h).1).occurrences (o.2.1.straight h (o.2.1.single h).1)
              ((Call.at call.1 call.2 env last).outputs (o.2.1.single h).1 env)
              ((Call.at call.1 call.2 env last).next last)),
          o.2.1.moved h env last,
          fun t p =>
            Identity.transport (History.Produced done)
              (All.lookupMap (fun _ i => env.lookup i) call.2 p).symm
              (known t (call.2.lookup p)),
          before.before (S.kind call.1)⟩
        (Diagram.Order.admissible (rest (o.2.1.single h).1) (o.1 (o.2.1.single h).1)
          (o.2.2 (o.2.1.single h).1) (o.2.1.straight h (o.2.1.single h).1)
          ((Call.at call.1 call.2 env last).outputs (o.2.1.single h).1 env)
          ((Call.at call.1 call.2 env last).next last)
          (⟨call.1, Call.at call.1 call.2 env last⟩ :: done)
          (Signature.Known.outputs (Call.at call.1 call.2 env last) (o.2.1.single h).1 known)
          (Effect.Produced.last (Call.at call.1 call.2 env last) before (S.kind call.1)))
  | _, _, .seq _ _, _, o, _, _, _, _, _, _ => nomatch o

/-- The number of the steps that a ready step passes is the same for each evidence that the
diagram is a diagram of the fragment. -/
def Diagram.Ready.depthSame {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (r : Diagram.Ready b d args after) : (s s' : d.Straight) → r.depth s ≡ r.depth s' :=
  Diagram.Ready.casesOn
    (motive := @fun _ _ d _ _ r => (s s' : d.Straight) → r.depth s ≡ r.depth s') r
    (fun _ _ _ _ => .refl)
    (@fun _ _ _ _ _ _ rest _ inner s s' =>
      Identity.cong Nat.succ
        (Identity.ind
          (fun (c : _) (_ : s.1.1 ≡ c) => (sc : (rest c).Straight) →
            (inner s.1.1).depth s.2 ≡ (inner c).depth sc)
          (fun sc => (inner s.1.1).depthSame s.2 sc) (s.1.2 s'.1.1) s'.2))

/-- A ready step of a diagram of the fragment that passes a given number of steps. -/
abbrev Diagram.ReadyAt {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight)
    (k : Nat) : Type :=
  (b : S.Op) × ((args : PortMap Γ (S.input b)) ×
    ((after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs) ×
      ((r : Diagram.Ready b d args after) × (r.depth h ≡ k))))

/-- A step that is ready in the rest of a first step is ready in the diagram, when the call of
the first step is not done, the call of each operand of the step is done, and the effectful
call before it is done. No operand is an output port of the first step, and one of the two
steps is pure. -/
def Diagram.readyPast {Γ : List Ty} {Qs : Exits Ty} (a : S.Op) (first : PortMap Γ (S.input a))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs)
    (h : (Diagram.step ⟨a, first⟩ rest).Straight) (env : All (History S Γ₀) Γ)
    (last : Option (Effect S Γ₀)) (done : List (S.Occurrence Γ₀))
    (fresh : Elem (⟨a, Call.at a first env last⟩ : S.Occurrence Γ₀) done → Empty)
    (k : Nat) (found : S.Occurrence Γ₀ × List (S.Occurrence Γ₀))
    (taken : takeAt k
        ((rest h.1.1).occurrences h.2 ((Call.at a first env last).outputs h.1.1 env)
          ((Call.at a first env last).next last)) ≡ some found)
    (operands : (t : Ty) → (p : Port (S.input found.1.1) t) →
      History.Produced done (found.1.2.args.lookup p))
    (effect : Effect.Produced done found.1.2.before)
    (ih : (rest h.1.1).ReadyAt h.2 k) :
    (Diagram.step ⟨a, first⟩ rest).ReadyAt h (k + 1) :=
  let A : Call S Γ₀ a := Call.at a first env last
  let env' : All (History S Γ₀) (h.1.1.1 ++ Γ) := A.outputs h.1.1 env
  let last' : Option (Effect S Γ₀) := A.next last
  let b : S.Op := ih.1
  let args' : PortMap (h.1.1.1 ++ Γ) (S.input b) := ih.2.1
  let r' := ih.2.2.2.1
  let sameOcc : found.1 ≡ (⟨b, Call.at b args' env' last'⟩ : S.Occurrence Γ₀) :=
    Identity.cong Prod.fst
      (Identity.someInject
        (taken.symm.trans
          ((Identity.cong
              (fun n => takeAt n ((rest h.1.1).occurrences h.2 env' last')) ih.2.2.2.2).symm.trans
            (r'.moved h.2 env' last'))))
  let ops : (t : Ty) → (p : Port (S.input b) t) →
      History.Produced done (All.lookup (env'.select args') p) :=
    Identity.transport
      (fun (x : S.Occurrence Γ₀) => (t : Ty) → (p : Port (S.input x.1) t) →
        History.Produced done (x.2.args.lookup p))
      sameOcc operands
  let eff : Effect.Produced done (Kind.before (S.kind b) last') :=
    Identity.transport (fun (x : S.Occurrence Γ₀) => Effect.Produced done x.2.before) sameOcc
      effect
  let strong := PortMap.strengthenBy h.1.1.1 args' fun t i j e =>
    fresh
      (Identity.transport (History.Produced done)
        ((All.lookupMap (fun _ q => env'.lookup q) args' i).trans
          ((Identity.cong (fun q => env'.lookup q) e).trans
            ((All.lookupLeft (All.tabulate h.1.1.1 fun _ q => History.output A h.1.1 q) env j).trans
              (All.lookupTabulate (fun _ q => History.output A h.1.1 q) j))))
        (ops t i))
  let central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure) :=
    match Kind.cases (S.kind a) with
    | .inl pa => .inl pa
    | .inr ea =>
        match Kind.cases (S.kind b) with
        | .inl pb => .inr pb
        | .inr eb =>
            (fresh
              (Identity.transport
                (fun k => Effect.Produced done (Kind.last k last (.after A))) ea
                (Identity.transport (fun k => Effect.Produced done (Kind.before k last')) eb
                  eff))).elim
  let r'' : Diagram.Ready b (rest h.1.1) (PortMap.weaken h.1.1.1 strong.1) ih.2.2.1 :=
    Identity.transport (fun x => Diagram.Ready b (rest h.1.1) x ih.2.2.1) strong.2 r'
  let sameDepth : r''.depth h.2 ≡ r'.depth h.2 :=
    Identity.ind (a := args')
      (fun (x : PortMap (h.1.1.1 ++ Γ) (S.input b)) (q : args' ≡ x) =>
        (Identity.transport (fun x => Diagram.Ready b (rest h.1.1) x ih.2.2.1) q r').depth h.2 ≡
          r'.depth h.2)
      .refl strong.2
  ⟨b, strong.1, _, (Diagram.Ready.pastOne a central first strong.1 h.1 r'').2,
    Identity.cong Nat.succ
      (Identity.ind (a := h.1.1)
        (fun (c : (S.output a).Case) (p : h.1.1 ≡ c) => (s' : (rest c).Straight) →
          ((Identity.transport
            (fun (c : (S.output a).Case) =>
              (aft : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) ×
                Diagram.Ready b (rest c) (PortMap.weaken c.1 strong.1) aft)
            p ⟨ih.2.2.1, r''⟩).2).depth s' ≡ k)
        (fun s' => (r''.depthSame s' h.2).trans (sameDepth.trans ih.2.2.2.2))
        (h.1.2 h.1.1) h.2)⟩

/-- The step of a diagram of the fragment at a number is ready, when no occurrence of the
diagram is done, the call of each operand of the step is done, and the effectful call before
it is done. -/
def Diagram.readyAt : (k : Nat) → {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (h : d.Straight) → (env : All (History S Γ₀) Γ) → (last : Option (Effect S Γ₀)) →
    (done : List (S.Occurrence Γ₀)) →
    ((x : S.Occurrence Γ₀) → Elem x (d.occurrences h env last) → Elem x done → Empty) →
    (found : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) →
    takeAt k (d.occurrences h env last) ≡ some found →
    ((t : Ty) → (p : Port (S.input found.1.1) t) →
      History.Produced done (found.1.2.args.lookup p)) →
    Effect.Produced done found.1.2.before → d.ReadyAt h k
  | 0, _, _, .exit _, _, _, _, _, _, _, p, _, _ => (Identity.noneNotSome p).elim
  | _ + 1, _, _, .exit _, _, _, _, _, _, _, p, _, _ => (Identity.noneNotSome p).elim
  | 0, _, _, .seq _ _, h, _, _, _, _, _, _, _, _ => nomatch h
  | _ + 1, _, _, .seq _ _, h, _, _, _, _, _, _, _, _ => nomatch h
  | 0, _, _, .step ⟨b, args⟩ rest, _, _, _, _, _, _, _, _, _ =>
      ⟨b, args, rest, .here args rest, .refl⟩
  | k + 1, _, _, .step ⟨a, first⟩ rest, h, env, last, done, fresh, _, taken, operands,
      effect =>
      let m := Identity.ofMapSome
        (takeAt k ((rest h.1.1).occurrences h.2 ((Call.at a first env last).outputs h.1.1 env)
          ((Call.at a first env last).next last))) taken
      let operands' := Identity.transport
        (fun (f : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) => (t : Ty) →
          (p : Port (S.input f.1.1) t) → History.Produced done (f.1.2.args.lookup p))
        m.2.2.symm operands
      let effect' := Identity.transport
        (fun (f : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) =>
          Effect.Produced done f.1.2.before)
        m.2.2.symm effect
      Diagram.readyPast a first rest h env last done (fresh _ .here) k m.1 m.2.1 operands'
        effect'
        (Diagram.readyAt k (rest h.1.1) h.2 ((Call.at a first env last).outputs h.1.1 env)
          ((Call.at a first env last).next last) done (fun x i j => fresh x (.there i) j) m.1
          m.2.1 operands' effect')

/-- The type with a value at each list that has an element. -/
def HasElement {α : Type} : List α → Type
  | [] => Empty
  | _ :: _ => Unit

/-- An admissible order of the occurrences of a diagram of the fragment is the word of an order
of the diagram, when no occurrence has two positions and no occurrence is done. The step of
each run is ready, and the order has the ready steps of the runs. -/
def Diagram.Order.ofAdmissible : (w : List Nat) → {Γ : List Ty} → {Qs : Exits Ty} →
    (d : Diagram S Γ Qs) → (h : d.Straight) → (env : All (History S Γ₀) Γ) →
    (last : Option (Effect S Γ₀)) → (done : List (S.Occurrence Γ₀)) →
    Separate (d.occurrences h env last) done →
    FreeDep (S.admissible Γ₀) (S.Finished Γ₀)
      ((word w).thread (E := Empty) (d.occurrences h env last, done)) →
    (e : Diagram S Γ Qs) × ((o : Diagram.Order e d) × (Diagram.Order.depths e d o h ≡ w))
  | [], _, _, .exit out, _, _, _, _, _, _ => ⟨.exit out, .refl, .refl⟩
  | [], _, _, .step _ _, _, _, _, _, _, ev =>
      (Identity.transport HasElement (FreeDep.result ev) ()).elim
  | [], _, _, .seq _ _, h, _, _, _, _, _ => nomatch h
  | k :: w, Γ, Qs, d, h, env, last, done, sep, ev =>
      let pre := (FreeDep.parts ev).1
      let ra := Diagram.readyAt k d h env last done sep.2 pre.1 pre.2.1 pre.2.2.1 pre.2.2.2
      let b : S.Op := ra.1
      let r := ra.2.2.2.1
      let B : Call S Γ₀ b := Call.at b ra.2.1 env last
      let c : (S.output b).Case := (r.single h).1
      let taken : takeAt k (d.occurrences h env last) ≡
          some ((⟨b, B⟩ : S.Occurrence Γ₀),
            (ra.2.2.1 c).occurrences (r.straight h c) (B.outputs c env) (B.next last)) :=
        (Identity.cong (fun n => takeAt n (d.occurrences h env last)) ra.2.2.2.2).symm.trans
          (r.moved h env last)
      let rec' := Diagram.Order.ofAdmissible w (ra.2.2.1 c) (r.straight h c) (B.outputs c env)
        (B.next last) (⟨b, B⟩ :: done) (Separate.take taken sep)
        (Identity.transport
          (fun (f : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) =>
            FreeDep (S.admissible Γ₀) (S.Finished Γ₀)
              ((word w).thread (E := Empty) (f.2, f.1 :: done)))
          (Identity.someInject (pre.2.1.symm.trans taken))
          ((FreeDep.parts ev).2 (.inr ((), (pre.1.2, pre.1.1 :: done))) .refl))
      let tail : (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (ra.2.2.1 c) :=
        ⟨rec'.1, rec'.2.1⟩
      let picked := Diagram.Order.pick b r (r.single h) tail
      ⟨picked.1, picked.2,
        Identity.cong₂ List.cons ra.2.2.2.2
          ((Identity.ind (a := c)
              (fun (c' : (S.output b).Case) (p : c ≡ c') =>
                Diagram.Order.depths
                    (Identity.transport
                      (fun (c : (S.output b).Case) =>
                        (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (ra.2.2.1 c))
                      p tail).1
                    (ra.2.2.1 c')
                    (Identity.transport
                      (fun (c : (S.output b).Case) =>
                        (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (ra.2.2.1 c))
                      p tail).2
                    (r.straight h c') ≡
                  Diagram.Order.depths tail.1 (ra.2.2.1 c) tail.2 (r.straight h c))
              .refl ((r.single h).2 c)).trans
            rec'.2.2)⟩

/-- An admissible order of the dependency graph of a diagram of the fragment with no two equal
occurrences is the word of an order of the diagram. -/
def Diagram.Order.ofGraph {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight)
    (distinct : Elem.Distinct (d.graph h)) (w : List Nat)
    (ev : FreeDep (S.admissible Γ) (S.Finished Γ) ((word w).thread (E := Empty) (d.graph h, []))) :
    (e : Diagram S Γ Qs) × ((o : Diagram.Order e d) × (Diagram.Order.depths e d o h ≡ w)) :=
  Diagram.Order.ofAdmissible w d h (S.inputs Γ) none [] (distinct, fun _ _ j => j.ofNil) ev

end Admissible

/-! The completeness of the list of the orders. -/

/-- The filter of the ready steps has a value at a ready step whose operands are operands of
the context before the first step, when one of the two steps is pure. -/
def Diagram.Choice.pastSome {Γ : List Ty} {Qs : Exits Ty} (a b : S.Op)
    (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs) (one : IsContr (S.output a).Case)
    {after₁ : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (one.1.1 ++ Γ)) Qs}
    (r₁ : Diagram.Ready b (rest one.1) (second.weaken one.1.1) after₁) :
    Diagram.Choice.past a first rest one ⟨b, second.weaken one.1.1, after₁, r₁⟩ ≡
      some ⟨b, second, _,
        (Diagram.Ready.pastOne a (Kind.centralOf central).1 first second one r₁).2⟩ :=
  Identity.cong₂
    (Diagram.Choice.pastOf a first rest one b (second.weaken one.1.1) r₁)
    (Kind.centralOf central).2 (PortMap.strengthenWeaken one.1.1 second)

/-- A ready step is in a list of ready steps of the diagram: a ready step of the list with the
same operation and operands, and a diagram after it that agrees at each case. -/
abbrev Diagram.Ready.ListedIn (b : S.Op) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (args : PortMap Γ (S.input b)) (after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs)
    (choices : List d.Choice) : Type :=
  (after' : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs) ×
    ((r' : Diagram.Ready b d args after') ×
      (Elem (⟨b, args, after', r'⟩ : d.Choice) choices ×
        ((cb : (S.output b).Case) → Diagram.Agreement (after cb) (after' cb))))

/-- A ready step is in the list of the ready steps of a diagram of the fragment. -/
abbrev Diagram.Ready.Listed (b : S.Op) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (args : PortMap Γ (S.input b)) (after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs)
    (h : d.Straight) : Type := Diagram.Ready.ListedIn b d args after (d.choices h)

/-- Each ready step is in the list of the ready steps, for each diagram of the fragment that
agrees with the diagram. -/
def Diagram.Ready.listed {b : S.Op} : {Γ : List Ty} → {Qs : Exits Ty} → {d : Diagram S Γ Qs} →
    {args : PortMap Γ (S.input b)} →
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs} →
    Diagram.Ready b d args after → (d' : Diagram S Γ Qs) → Diagram.Agreement d d' →
    (h' : d'.Straight) → Diagram.Ready.Listed b d' args after h'
  | _, _, _, _, _, .here args _, _, same, h' =>
      same.view (fun d' => (h' : d'.Straight) → Diagram.Ready.Listed b d' args _ h')
        (fun rest' each _ => ⟨rest', .here args rest', .here, each⟩) h'
  | Γ, _, _, _, _, @Diagram.Ready.past _ _ _ _ _ a central first second _ after inner, _, same,
      h' =>
      same.view (fun d' => (h' : d'.Straight) → Diagram.Ready.Listed b d' second _ h')
        (fun rest' each h' =>
          let ih := Diagram.Ready.listed (inner h'.1.1) (rest' h'.1.1) (each h'.1.1) h'.2
          let po := Diagram.Ready.pastOne a (Kind.centralOf central).1 first second h'.1
            ih.2.1
          ⟨_, po.2,
            .there (Elem.ofFilterMap ih.2.2.1
              (Diagram.Choice.pastSome a b central first second rest' h'.1 ih.2.1)),
            fun cb => .step _ fun ca =>
              Diagram.Agreement.rename (PortMap.exchange ca.1 cb.1 Γ)
                (Identity.ind
                  (fun (c : (S.output a).Case) (p : h'.1.1 ≡ c) =>
                    (cb : (S.output b).Case) →
                    Diagram.Agreement (after c cb)
                      ((Identity.transport
                        (fun (c : (S.output a).Case) =>
                          (aft : (cb : (S.output b).Case) →
                              Diagram S (cb.1 ++ (c.1 ++ Γ)) _) ×
                            Diagram.Ready b (rest' c) (second.weaken c.1) aft)
                        p ⟨ih.1, ih.2.1⟩).1 cb))
                  (fun cb => ih.2.2.2 cb) (h'.1.2 ca) cb)⟩)
        h'

/-- A ready step is the ready step of its own call, with its own evidence. -/
private def Diagram.Choice.atSelf [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs}
    (k : d.Choice) : k.atCall ⟨k.1, k.2.1⟩ ≡ some k.2.2 :=
  let call : (S.interface (Port Γ)).Shape := ⟨k.1, k.2.1⟩
  Identity.cong (Dec.transport? d.ReadyFor k.2.2)
    (Dec.yesRefl (Dec.sigma (P := fun b => PortMap Γ (S.input b)) decideEq
      (fun _ => All.decide (fun _ => Elem.decide))) call)

/-- The list of the ready steps of a test with two cases is complete for the moves before the
test. A step that is ready in the rest of each case, with operands of the context of the test,
is in the list, with a diagram after it that agrees at each case. This holds also when one
case has two calls with the same operation and the same operands. -/
def Diagram.Ready.pastListed [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (a b : S.Op)
    (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    (first : PortMap Γ (S.input a)) (args : PortMap Γ (S.input b))
    (rest : (c : (S.output a).Case) → Diagram S (c.1 ++ Γ) Qs)
    (two : (S.output a).Binary) (arms : (c : (S.output a).Case) → (rest c).Straight)
    {after : (ca : (S.output a).Case) → (cb : (S.output b).Case) →
      Diagram S (cb.1 ++ (ca.1 ++ Γ)) Qs}
    (inner : (ca : (S.output a).Case) → Diagram.Ready b (rest ca) (args.weaken ca.1) (after ca)) :
    Diagram.Ready.ListedIn b (.step ⟨a, first⟩ rest) args
      (fun cb => .step ⟨a, first.weaken cb.1⟩ fun ca =>
        Diagram.rename (PortMap.exchange ca.1 cb.1 Γ) (after ca cb))
      (Diagram.binaryChoices a first rest two arms) :=
  let listed (c : (S.output a).Case) := (inner c).listed (rest c) (.refl _) (arms c)
  let arm (c : (S.output a).Case) : (rest c).ReadyFor ⟨b, args.weaken c.1⟩ :=
    ⟨(listed c).1, (listed c).2.1⟩
  let choice (c : (S.output a).Case) : (rest c).Choice := ⟨b, args.weaken c.1, arm c⟩
  let ok := Kind.centralOf central
  let pair := Diagram.Ready.pastBinary a first rest two ok.1 args (arm two.left) (arm two.right)
  let found : (Diagram.step ⟨a, first⟩ rest).Choice := ⟨b, args, pair⟩
  let matchLeft := Diagram.Choice.matchRight a first rest two (choice two.left)
    ((rest two.right).choices (arms two.right))
  let mem : Elem found (matchLeft (some ok.1) (some ⟨args, .refl⟩)) :=
    Elem.ofFilterMap (listed two.right).2.2.1
      (Identity.cong (Option.map fun right =>
        (⟨b, args, Diagram.Ready.pastBinary a first rest two ok.1 args (arm two.left) right⟩ :
          (Diagram.step ⟨a, first⟩ rest).Choice)) (Diagram.Choice.atSelf (choice two.right)))
  ⟨pair.1, pair.2,
    .there (Elem.ofFlatMap (listed two.left).2.2.1
      (Identity.transport (Elem found)
        (Identity.cong₂ matchLeft ok.2 (PortMap.strengthenWeaken two.left.1 args)).symm mem)),
    fun cb => .step _ fun ca => Diagram.Agreement.rename (PortMap.exchange ca.1 cb.1 Γ)
      (two.elimAt (F := fun c => (rest c).ReadyFor ⟨b, args.weaken c.1⟩)
        (fun c residual => Diagram.Agreement (after c cb) (residual.1 cb))
        ((listed two.left).2.2.2 cb) ((listed two.right).2.2.2 cb) ca)⟩

/-- The diagram after a ready step of a diagram of the fragment has one step less. -/
def Diagram.Ready.opsAfter {b : S.Op} : {Γ : List Ty} → {Qs : Exits Ty} →
    {d : Diagram S Γ Qs} → {args : PortMap Γ (S.input b)} →
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs} →
    (r : Diagram.Ready b d args after) → (h : d.Straight) →
    ((after (r.single h).1).ops (r.straight h (r.single h).1)).length + 1 ≡ (d.ops h).length
  | _, _, _, _, _, .here _ rest, h =>
      Identity.cong (fun k => k + 1)
        (Identity.ind
          (fun (c : (S.output b).Case) (p : h.1.1 ≡ c) =>
            ((rest c).ops (Identity.transport (fun c => (rest c).Straight) p h.2)).length ≡
              ((rest h.1.1).ops h.2).length)
          .refl (h.1.2 h.1.1))
  | Γ, _, _, _, _, @Diagram.Ready.past _ _ _ _ _ _ _ _ _ _ after inner, h =>
      Identity.cong (fun k => k + 1)
        ((Identity.cong (fun (l : List S.Op) => l.length + 1)
            (Diagram.opsRename (PortMap.exchange h.1.1.1 _ Γ) (after h.1.1 _)
              ((inner h.1.1).straight h.2 _))).trans
          (Diagram.Ready.opsAfter (inner h.1.1) h.2))

/-- The order with a ready step of the list first, and then an order of the list of the diagram
after that step, is an order of the list. -/
def Diagram.Order.pickListed : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    (h : d.Straight) → (choice : d.Choice) → Elem choice (d.choices h) → (m : Nat) →
    (tail : (e : Diagram S ((choice.2.2.2.single h).1.1 ++ Γ) Qs) ×
      Diagram.Order e (choice.2.2.1 (choice.2.2.2.single h).1)) →
    Elem tail
      (Diagram.ordersWithin m (choice.2.2.1 (choice.2.2.2.single h).1)
        (choice.2.2.2.straight h (choice.2.2.2.single h).1)) →
    Elem
      (Diagram.Order.pick choice.1 choice.2.2.2 (choice.2.2.2.single h) tail)
      (Diagram.ordersWithin (m + 1) d h)
  | _, _, .exit _, _, _, mem, _, _, _ => mem.ofNil
  | _, _, .step _ _, h, choice, mem, _, _, memTail =>
      Elem.ofFlatMap mem
        (Elem.map
          (fun tail =>
            Diagram.Order.pick choice.1 choice.2.2.2 (choice.2.2.2.single h) tail)
          memTail)
  | _, _, .seq _ _, h, _, _, _, _, _ => nomatch h

/-- An order of the list of a diagram that agrees with a diagram. -/
abbrev Diagram.Order.Listed {Γ : List Ty} {Qs : Exits Ty} (e d : Diagram S Γ Qs) (h : d.Straight)
    (n : Nat) : Type :=
  (r : (e' : Diagram S Γ Qs) × Diagram.Order e' d) ×
    (Elem r (Diagram.ordersWithin n d h) × Diagram.Agreement e r.1)

/-- Each order of a diagram agrees with an order of the list, for each diagram of the fragment
that agrees with the diagram and each bound that is the number of its steps. -/
def Diagram.Order.listedWithin : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) →
    Diagram.Order e d → (d' : Diagram S Γ Qs) → Diagram.Agreement d d' → (h' : d'.Straight) →
    (n : Nat) → (d'.ops h').length ≡ n → Diagram.Order.Listed e d' h' n
  | Γ, Qs, .exit out, _, o, d', same, h', n, _ =>
      Identity.ind
        (fun (d : Diagram S Γ Qs) _ => (d' : Diagram S Γ Qs) → Diagram.Agreement d d' →
          (h' : d'.Straight) → (n : Nat) → Diagram.Order.Listed (.exit out) d' h' n)
        (fun (d' : Diagram S Γ Qs) (same : Diagram.Agreement (Diagram.exit out) d') h' n =>
          same.view
            (fun d' => (h' : d'.Straight) → (n : Nat) → Diagram.Order.Listed (.exit out) d' h' n)
            (fun _ n =>
              match n with
              | 0 => ⟨⟨.exit out, .refl⟩, .here, Diagram.Agreement.refl _⟩
              | _ + 1 => ⟨⟨.exit out, .refl⟩, .here, Diagram.Agreement.refl _⟩)
            h' n)
        o d' same h' n
  | Γ, Qs, .step call rest, _, o, d', same, h', _, fuel =>
      let found := o.2.1.listed d' same h'
      let c := (found.2.1.single h').1
      let only := (found.2.1.single h').2
      let ih := Diagram.Order.listedWithin (rest c) (o.1 c) (o.2.2 c) (found.1 c)
        (found.2.2.2 c) (found.2.1.straight h' c) _ .refl
      Identity.transport (fun n => Diagram.Order.Listed (.step call rest) d' h' n)
        ((found.2.1.opsAfter h').trans fuel)
        ⟨Diagram.Order.pick call.1 found.2.1 (found.2.1.single h') ih.1,
          Diagram.Order.pickListed d' h' ⟨call.1, call.2, found.1, found.2.1⟩ found.2.2.1 _ ih.1
            ih.2.1,
          .step call fun cb =>
            Identity.ind
              (fun (cb : (S.output call.1).Case) (p : c ≡ cb) =>
                Diagram.Agreement (rest cb)
                  (Identity.transport
                    (fun (c : (S.output call.1).Case) =>
                      (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (found.1 c))
                    p ih.1).1)
              ih.2.2 (only cb)⟩
  | _, _, .seq _ _, _, o, _, _, _, _, _ => nomatch o

/-- Each order of a diagram of the fragment agrees with an order of the list of its orders. -/
def Diagram.Order.listed {Γ : List Ty} {Qs : Exits Ty} (e d : Diagram S Γ Qs)
    (o : Diagram.Order e d) (h : d.Straight) :
    (r : (e' : Diagram S Γ Qs) × Diagram.Order e' d) ×
      (Elem r (d.orders h) × Diagram.Agreement e r.1) :=
  Diagram.Order.listedWithin e d o d (Diagram.Agreement.refl d) h _ .refl

end Draft
