import Draft.Diagram

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

A schedule of a diagram is the choice of one ready step at each point, and then a schedule of
the diagram after that step at each output case. The realization of a schedule is the diagram
with the steps in the order of the choices. The derivation from the diagram to the realization
has one application of the theorem for each choice. -/

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
    {b : S.Op} : {Γ : List Ty} → {Qs : Exits Ty} → {d : Diagram S Γ Qs} →
    {args : PortMap Γ (S.input b)} →
    {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs} →
    Diagram.Ready b d args after → Diagram.Derivation R d (.step ⟨b, args⟩ after)
  | _, _, _, _, _, @Diagram.Ready.here _ _ _ _ _ args rest =>
      .agree (.refl (.step ⟨b, args⟩ rest))
  | _, _, _, _, _, @Diagram.Ready.past _ _ _ _ _ a central first second _ after inner =>
      .trans (.step ⟨a, first⟩ fun ca => (inner ca).derivation inter)
        (.rule (inter.diagram (.swap a b central first second after)))

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

/-- A schedule of a diagram: the choice of one ready step at each point, and a schedule of the
diagram after that step at each output case. -/
inductive Diagram.Schedule : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Type where
  | exit {Γ : List Ty} {Qs : Exits Ty} (out : Qs.At (Port Γ)) : Diagram.Schedule (.exit out)
  | pick {Γ : List Ty} {Qs : Exits Ty} {d : Diagram S Γ Qs} (b : S.Op)
      {args : PortMap Γ (S.input b)}
      {after : (cb : (S.output b).Case) → Diagram S (cb.1 ++ Γ) Qs}
      (ready : Diagram.Ready b d args after)
      (next : (cb : (S.output b).Case) → Diagram.Schedule (after cb)) : Diagram.Schedule d

/-- The realization of a schedule: the diagram with the steps in the order of the choices. -/
def Diagram.Schedule.realization : {Γ : List Ty} → {Qs : Exits Ty} → {d : Diagram S Γ Qs} →
    Diagram.Schedule d → Diagram S Γ Qs
  | _, _, _, @Diagram.Schedule.exit _ _ _ _ out => .exit out
  | _, _, _, @Diagram.Schedule.pick _ _ _ _ _ b args _ _ next =>
      .step ⟨b, args⟩ fun cb => (next cb).realization

/-- The derivation from a diagram to the realization of a schedule, in each rule set that has
the interchange rule: one move of a ready step for each choice. -/
def Diagram.Schedule.derivation {R : Rules S} (inter : Rules.Map (Rules.interchange S) R) :
    {Γ : List Ty} → {Qs : Exits Ty} → {d : Diagram S Γ Qs} → (s : Diagram.Schedule d) →
    Diagram.Derivation R d s.realization
  | _, _, _, @Diagram.Schedule.exit _ _ _ _ out => .agree (.refl (.exit out))
  | _, _, _, @Diagram.Schedule.pick _ _ _ _ _ b args _ ready next =>
      .trans (ready.derivation inter) (.step ⟨b, args⟩ fun cb => (next cb).derivation inter)

end Draft
