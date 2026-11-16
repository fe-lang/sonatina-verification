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
with the theorem of the move as the witness of each precondition. -/

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
        (Diagram.occurrencesCase rest (h.2.1 h.1) h.2.2 (Call.at b args env last) env
          ((Call.at b args env last).next last)))
    (@fun _ _ a central first second rest after inner h env last =>
      Diagram.movedPast a b central first second h.1 ((inner h.1).single h.2.2).1
        (after h.1 ((inner h.1).single h.2.2).1)
        ((inner h.1).straight h.2.2 ((inner h.1).single h.2.2).1) env last
        (takeAt ((inner h.1).depth h.2.2)
          ((rest h.1).occurrences h.2.2 ((Call.at a first env last).outputs h.1 env)
            ((Call.at a first env last).next last)))
        ((inner h.1).moved h.2.2 ((Call.at a first env last).outputs h.1 env)
          ((Call.at a first env last).next last)))

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

end Admissible

end Draft
