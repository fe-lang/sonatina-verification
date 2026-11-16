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
order are diagrams of the fragment. -/

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
cases has a center, and each case is identical to the center. The evidence in the rest at the
center gives the evidence at each case. -/
def Diagram.Ready.pastOne {b : S.Op} {Γ : List Ty} {Qs : Exits Ty} (a : S.Op)
    (central : (S.kind a ≡ .pure) ⊕ (S.kind b ≡ .pure))
    (first : PortMap Γ (S.input a)) (second : PortMap Γ (S.input b))
    {rest : (ca : (S.output a).Case) → Diagram S (ca.1 ++ Γ) Qs}
    (center : (S.output a).Case) (only : (c : (S.output a).Case) → center ≡ c)
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ (center.1 ++ Γ)) Qs}
    (inner : Diagram.Ready b (rest center) (second.weaken center.1) after) :
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
      (only ca) ⟨after, inner⟩
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
    d.Straight → (center : (S.output b).Case) × ((c : (S.output b).Case) → center ≡ c) :=
  Diagram.Ready.casesOn
    (motive := @fun _ _ d _ _ _ =>
      d.Straight → (center : (S.output b).Case) × ((c : (S.output b).Case) → center ≡ c))
    r
    (fun _ _ h => ⟨h.1, h.2.1⟩)
    (@fun _ _ _ _ _ _ _ _ inner h => (inner h.1).single h.2.2)

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
    (fun _ rest h cb => Identity.transport (fun c => (rest c).Straight) (h.2.1 cb) h.2.2)
    (@fun Γ _ _ _ _ _ _ after inner h cb =>
      ⟨h.1, h.2.1,
        Diagram.Straight.rename (PortMap.exchange h.1.1 cb.1 Γ) (after h.1 cb)
          ((inner h.1).straight h.2.2 cb)⟩)

/-- An order of a diagram of the fragment is a diagram of the fragment. -/
def Diagram.Order.straight : {Γ : List Ty} → {Qs : Exits Ty} → (e d : Diagram S Γ Qs) →
    Diagram.Order e d → d.Straight → e.Straight
  | _, _, .exit _, _, _, _ => ()
  | _, _, .step _ rest, _, o, h =>
      ⟨(o.2.1.single h).1, (o.2.1.single h).2,
        Diagram.Order.straight (rest (o.2.1.single h).1) (o.1 (o.2.1.single h).1)
          (o.2.2 (o.2.1.single h).1) (o.2.1.straight h (o.2.1.single h).1)⟩
  | _, _, .seq _ _, _, o, _ => nomatch o

/-- A ready step of a diagram: its operation, its operands, the diagram after it, and the
evidence. -/
abbrev Diagram.Choice {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) : Type :=
  (b : S.Op) × ((args : PortMap Γ (S.input b)) ×
    ((after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs) ×
      Diagram.Ready b d args after))

/-- The ready steps of a diagram of the fragment, in the order of its steps. The first step is
ready. A ready step of its rest is ready when one of the two steps is pure, and its operands
have no output port of the first step. -/
def Diagram.choices : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    List d.Choice
  | _, _, .exit _, _ => []
  | _, _, .step ⟨a, first⟩ rest, h =>
      ⟨a, first, rest, .here first rest⟩ ::
        (Diagram.choices (rest h.1) h.2.2).filterMap fun choice =>
          match Kind.central (S.kind a) (S.kind choice.1) with
          | none => none
          | some central =>
              match PortMap.strengthen h.1.1 choice.2.1 with
              | none => none
              | some outer =>
                  some ⟨choice.1, outer.1, _,
                    (Diagram.Ready.pastOne a central first outer.1 h.1 h.2.1
                      (Identity.transport
                        (fun x => Diagram.Ready choice.1 (rest h.1) x choice.2.2.1) outer.2
                        choice.2.2.2)).2⟩
  | _, _, .seq _ _, _ => []

/-- The order with a ready step first, from an order of the diagram after that step at the
center of the output cases of the step. The order at the center gives the order at each
case. -/
def Diagram.Order.pick {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs} (b : S.Op)
    {args : PortMap Γ (S.input b)}
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
    (ready : Diagram.Ready b d args after) (center : (S.output b).Case)
    (only : (c : (S.output b).Case) → center ≡ c)
    (tail : (e : Diagram S (center.1 ++ Γ) Qs) × Diagram.Order e (after center)) :
    (e : Diagram S Γ Qs) × Diagram.Order e d :=
  let spread (cb : (S.output b).Case) :
      (e : Diagram S (cb.1 ++ Γ) Qs) × Diagram.Order e (after cb) :=
    Identity.transport
      (fun (c : (S.output b).Case) =>
        (e : Diagram S (c.1 ++ Γ) Qs) × Diagram.Order e (after c))
      (only cb) tail
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
          Diagram.Order.pick choice.1 choice.2.2.2 (choice.2.2.2.single h).1
            (choice.2.2.2.single h).2 tail
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
    (@fun _ _ _ _ _ _ _ _ inner h => (inner h.1).depth h.2.2 + 1)

/-- The element at a number in a list, with the other elements in their order. -/
def takeAt {α : Type} : Nat → List α → Option (α × List α)
  | _, [] => none
  | 0, a :: rest => some (a, rest)
  | k + 1, a :: rest =>
      match takeAt k rest with
      | none => none
      | some found => some (found.1, a :: found.2)

/-- The names of the steps of an order of a diagram of the fragment, from the names of the
steps of the diagram: each step of the order has the name of its ready step. -/
def Diagram.Order.names {N : Type} : {Γ : List Ty} → {Qs : Exits Ty} →
    (e d : Diagram S Γ Qs) → Diagram.Order e d → d.Straight → List N → List N
  | _, _, .exit _, _, _, _, _ => []
  | _, _, .step _ rest, _, o, h, names =>
      match takeAt (o.2.1.depth h) names with
      | none => []
      | some found =>
          found.1 ::
            Diagram.Order.names (rest (o.2.1.single h).1) (o.1 (o.2.1.single h).1)
              (o.2.2 (o.2.1.single h).1) (o.2.1.straight h (o.2.1.single h).1) found.2
  | _, _, .seq _ _, _, o, _, _ => nomatch o

end Draft
