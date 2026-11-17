import Draft.Verified

/-! Diagrams with a runtime.

A machine of the request interface of a signature has a runtime: for a call and a runtime it
gives a response with the next runtime, or it stops. The run of the function meaning of a
diagram on a machine has the runtime at each call in sequence.

A derivation in a rule set that holds after the substitution of a lowering gives an agreement
of the two computations with a runtime, after the lowering with a runtime. A verified
implementation with a runtime moves along the agreement. Such a rule set holds on the machine
of the lowering, for each machine of the target.

A rule set can hold on a machine and not after a substitution: the two sides of a rule can have
different calls and one run. A derivation in such a rule set gives the identity of the machines
of its two diagrams at each call. The evidence of the machine of the first diagram moves along
that identity to the machine of the second diagram, for each specification of the interface of
the diagram with a runtime.

A cell of a signature at a value type is a read with no operand and one output port, and a
write with one operand and no output port. The equations of global state are five equations
between closed sequences of steps of a cell. Each equation gives a theorem for each context and
each rest: a derivation in the control equation set with the equations of global state.

The cell is a morphism from the interface of a cell to the request interface of the signature,
for each family of values. The equation set of global state holds on each machine that is, at
the calls of the cell, the machine of a cell along a lawful lens of the runtime. -/

set_option autoImplicit false
set_option genInjectivity false

universe w z p w' u v

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type} {R : Type} {E : Type}

section Derivation

variable {D : Container.{u, v}} {lower : Impl (S.interface X) D} {T : Rules S} {α : Type}
  (stop : Free (S.interface X) α) (count : Nat)
  (ok : T.Sound (Free.Congruence.subst (α := α) lower))

/-- A derivation in a rule set that holds after the substitution of a lowering gives
computations with a runtime that agree, after the lowering with a runtime. -/
def Diagram.Derivation.thread {Γ : List Ty} {Qs : Exits Ty} {d e : Diagram S Γ Qs}
    (h : Diagram.Derivation T d e) (env : All X Γ) (rest : Qs.At X → Free (S.interface X) α)
    (s : R) :
    Free.Agreement (((d.run stop count env rest).thread (E := E) s).subst lower.thread)
      (((e.run stop count env rest).thread s).subst lower.thread) :=
  (Free.threadSubst lower (d.run stop count env rest) s).symm.trans
    ((Free.Agreement.thread (h.sound stop count ok env rest) s).trans
      (Free.threadSubst lower (e.run stop count env rest) s))

/-- The two continuations of a derivation, with a runtime. -/
def Continuation.Derivation.thread {K : Boundary Ty} {Qs : Exits Ty} {k k' : Continuation S K Qs}
    (h : Continuation.Derivation T k k') (a : K.At X) (rest : Qs.At X → Free (S.interface X) α)
    (s : R) :
    Free.Agreement (((k.run stop count a rest).thread (E := E) s).subst lower.thread)
      (((k'.run stop count a rest).thread s).subst lower.thread) :=
  (Free.threadSubst lower (k.run stop count a rest) s).symm.trans
    ((Free.Agreement.thread (h.sound stop count ok a rest) s).trans
      (Free.threadSubst lower (k'.run stop count a rest) s))

/-- Rules that hold after the substitution of a lowering hold on the machine of the lowering,
for each machine of the target. -/
def Rules.Sound.machine (m : Machine D R E) : T.Sound (α := α) (m.impl lower).congruence :=
  ok.map (Machine.runOfSubst lower m)

end Derivation

/-- A derivation in a rule set that holds after the substitution of a lowering gives a map of
verified implementations with a runtime, of one specification. The agreement of the two
computations with a runtime is its plain part, and the lift moves along it. -/
def Diagram.Derivation.stateLift {D : Container.{0, 0}} {lower : Impl (S.interface X) D}
    {T : Rules S} {Γ : List Ty} {Qs : Exits Ty}
    (ok : T.Sound (Free.Congruence.subst (α := Qs.At X) lower))
    {d e : Diagram S Γ Qs} (h : Diagram.Derivation T d e)
    {q : DepPoly.{0, 0, w', p} ((Diagram.interface X Γ Qs).runtime R E)}
    {t : DepPoly.{0, 0, w, z} (D.runtime R E)} (stop : Free (S.interface X) (Qs.At X))
    (count : Nat) (ff : ImplDep q t ((d.impl stop count).thread.trans lower.thread)) :
    ImplDep q t ((e.impl stop count).thread.trans lower.thread) :=
  ImplDep.reindex (fun a => h.thread stop count ok a.1 .pure a.2) ff

section Machine

variable {m : Machine (S.interface X) R E} {T : Rules S} {Γ : List Ty} {Qs : Exits Ty}
  (ok : T.Sound (α := Qs.At X) m.congruence) {d e : Diagram S Γ Qs}
  (h : Diagram.Derivation T d e) (stop : Free (S.interface X) (Qs.At X)) (count : Nat)

/-- The two diagrams of a derivation have one machine, on each machine on which the rules
hold. -/
def Diagram.Derivation.machine :
    Homotopy (m.impl (d.impl stop count)) (m.impl (e.impl stop count)) :=
  fun a => h.sound stop count ok a.1 .pure a.2

/-- A derivation in a rule set that holds on a machine gives a map of the evidence of the
machine of a diagram, for one specification. The identity of the two machines at each call is
its plain part, and the evidence moves along it. -/
def Diagram.Derivation.evidence
    {q : DepPoly.{0, 0, w, z} ((Diagram.interface X Γ Qs).runtime R E)}
    (ev : Evidence q (m.impl (d.impl stop count))) : Evidence q (m.impl (e.impl stop count)) :=
  Evidence.reindex (h.machine ok stop count) ev

end Machine

section Cell

variable {τ : Ty}

/-- A cell of a signature at a value type: a read with no operand and one output port, and a
write with one operand and no output port. -/
structure Signature.Cell (S : Signature Ty) (τ : Ty) where
  read : S.Op
  write : S.Op
  readInput : [] ≡ S.input read
  readOutput : Boundary.one [τ] ≡ S.output read
  writeInput : [τ] ≡ S.input write
  writeOutput : Boundary.one [] ≡ S.output write

namespace Signature.Cell

variable (cell : S.Cell τ)

/-- A read, and then the rest with the value. -/
def get {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S (τ :: Γ) Qs) : Diagram S Γ Qs :=
  .step ⟨cell.read, Identity.transport (PortMap Γ) cell.readInput .nil⟩
    (Diagram.oneAt cell.readOutput d)

/-- A write of a port, and then the rest. -/
def put {Γ : List Ty} {Qs : Exits Ty} (v : Port Γ τ) (d : Diagram S Γ Qs) : Diagram S Γ Qs :=
  .step ⟨cell.write, Identity.transport (PortMap Γ) cell.writeInput (.cons v .nil)⟩
    (Diagram.oneAt (Δ := []) cell.writeOutput d)

end Signature.Cell

/-- The five equations of global state for a cell. Each side is a closed sequence of steps
with one exit. -/
inductive Diagram.GlobalState (cell : S.Cell τ) : {Γ : List Ty} → {Qs : Exits Ty} →
    Diagram S Γ Qs → Diagram S Γ Qs → Type where
  /-- Two reads give one value: `get ; (X ⊗ get) = get ; copy`. The exit of the two reads has
  the two values in the order of the context. -/
  | getGet : Diagram.GlobalState cell (Γ := [])
      (cell.get (cell.get (.exitOne (.cons .here (.cons (.there .here) .nil)))))
      (cell.get (.exitOne (.cons .here (.cons .here .nil))))
  /-- A read whose value has no use does nothing: `get ; discard = id`. -/
  | getDiscard : Diagram.GlobalState cell (Γ := []) (cell.get (.exitOne .nil)) (.exitOne .nil)
  /-- Of two writes, the last one stays: `(put ⊗ X) ; put = (discard ⊗ X) ; put`. -/
  | putPut : Diagram.GlobalState cell (Γ := [τ, τ])
      (cell.put .here (cell.put (.there .here) (.exitOne .nil)))
      (cell.put (.there .here) (.exitOne .nil))
  /-- A read and then a write of its value does nothing: `get ; put = id`. -/
  | getPut : Diagram.GlobalState cell (Γ := []) (cell.get (cell.put .here (.exitOne .nil)))
      (.exitOne .nil)
  /-- A write and then a read gives the written value: `put ; get = copy ; (put ⊗ X)`. -/
  | putGet : Diagram.GlobalState cell (Γ := [τ])
      (cell.put .here (cell.get (.exitOne (.cons .here .nil))))
      (cell.put .here (.exitOne (.cons .here .nil)))

/-- The equation set of global state for a cell. -/
def Rules.globalState (cell : S.Cell τ) : Rules S := ⟨Diagram.GlobalState cell, fun _ _ => Empty⟩

/-- The control equation set with the equations of global state for the cell. -/
abbrev Signature.Cell.rules (cell : S.Cell τ) : Rules S :=
  (Rules.control S).sum (Rules.globalState cell)

section Inline

variable (cell : S.Cell τ) {M K : Boundary Ty} {Qs : Exits Ty} (j : M.Case)
  (each : (p : (M.product K).Case) → Diagram S p.1 Qs) {Γ Δ : List Ty} (ξ : PortMap Γ j.1)
  (args : PortMap Γ Δ)

/-- A read in a context with the rest in line is the read, and then the rest of the read in
the context with the value. -/
def Signature.Cell.inlineGet (x : Diagram S (τ :: Δ) [K]) {y : Diagram S (τ :: Γ) Qs}
    (same : Diagram.Agreement
      (Diagram.inline j each (PortMap.weaken [τ] ξ) (args.lift [τ]) x) y) :
    Diagram.Agreement (Diagram.inline j each ξ args (cell.get x)) (cell.get y) :=
  Diagram.Agreement.stepPorts cell.read (PortMap.selectTransport cell.readInput .nil args)
    (Diagram.oneAtAgree cell.readOutput
      (fun Ξ x => Diagram.inline j each (PortMap.weaken Ξ ξ) (args.lift Ξ) x) same)

/-- A write in a context with the rest in line is the write of the port that the port map
gives, and then the rest of the write in the context. -/
def Signature.Cell.inlinePut (p : Port Δ τ) (x : Diagram S Δ [K]) {y : Diagram S Γ Qs}
    (same : Diagram.Agreement
      (Diagram.inline j each (PortMap.weaken [] ξ) (args.lift []) x) y) :
    Diagram.Agreement (Diagram.inline j each ξ args (cell.put p x))
      (cell.put (args.lookup p) y) :=
  Diagram.Agreement.stepPorts cell.write
    (PortMap.selectTransport cell.writeInput (.cons p .nil) args)
    (Diagram.oneAtAgree (Δ := []) cell.writeOutput
      (fun Ξ x => Diagram.inline j each (PortMap.weaken Ξ ξ) (args.lift Ξ) x) same)

end Inline

section Laws

variable (cell : S.Cell τ) {Γ : List Ty} {Qs : Exits Ty}

/-- Two reads give one value, in each context and with each rest: the rest has the value of
the one read at its first two ports. -/
def Signature.Cell.getGet (d : Diagram S (τ :: τ :: Γ) Qs) :
    Diagram.Derivation cell.rules (cell.get (cell.get d))
      (cell.get (Diagram.rename (.cons .here (PortMap.id (τ :: Γ))) d)) :=
  let each := Diagram.restOne (Γ := Γ) (Δ := [τ, τ]) d
  let ξ₁ : PortMap (τ :: Γ) Γ := PortMap.weaken [τ] (PortMap.id Γ)
  let a₁ : PortMap (τ :: Γ) [τ] := PortMap.lift [τ] (All.nil (P := Port Γ))
  Diagram.Derivation.trans (R := cell.rules)
    (Diagram.Derivation.symm
      (.agree
        (cell.inlineGet (Boundary.only Γ) each (PortMap.id Γ) .nil
          (cell.get (.exitOne (.cons .here (.cons (.there .here) .nil))))
          (cell.inlineGet (Boundary.only Γ) each ξ₁ a₁
            (.exitOne (.cons .here (.cons (.there .here) .nil)))
            (Diagram.renameAgree d _
              ((Identity.cong
                  (fun (ζ : PortMap (τ :: τ :: Γ) Γ) =>
                    (All.cons (P := Port (τ :: τ :: Γ)) Elem.here
                      (All.cons (Elem.there Elem.here) ζ) :
                      PortMap (τ :: τ :: Γ) (τ :: τ :: Γ)))
                  (All.mapMap _ _ (PortMap.id Γ))).trans
                (PortMap.liftId [τ, τ] Γ)))))))
    (Diagram.Derivation.trans (R := cell.rules)
      (Diagram.Derivation.inline (Boundary.only Γ) each (Rules.Map.inl _ _)
        (Diagram.Derivation.rule (R := cell.rules) (Sum.inr Diagram.GlobalState.getGet))
        (PortMap.id Γ) .nil)
      (.agree
        (cell.inlineGet (Boundary.only Γ) each (PortMap.id Γ) .nil
          (.exitOne (.cons .here (.cons .here .nil)))
          (Diagram.Agreement.renamePorts d
            (Identity.cong (All.cons (P := Port (τ :: Γ)) Elem.here)
              (PortMap.liftId [τ] Γ))))))

/-- A read whose value has no use does nothing, in each context and with each rest. -/
def Signature.Cell.getDiscard (d : Diagram S Γ Qs) :
    Diagram.Derivation cell.rules
      (cell.get (Diagram.rename (PortMap.weaken [τ] (PortMap.id Γ)) d)) d :=
  let each := Diagram.restOne (Γ := Γ) (Δ := []) d
  Diagram.Derivation.trans (R := cell.rules)
    (Diagram.Derivation.symm
      (.agree
        (cell.inlineGet (Boundary.only Γ) each (PortMap.id Γ) .nil (.exitOne .nil)
          (Diagram.Agreement.refl _))))
    (Diagram.Derivation.trans (R := cell.rules)
      (Diagram.Derivation.inline (Boundary.only Γ) each (Rules.Map.inl _ _)
        (Diagram.Derivation.rule (R := cell.rules) (Sum.inr Diagram.GlobalState.getDiscard))
        (PortMap.id Γ) .nil)
      (.agree (Diagram.renameId d)))

/-- Of two writes, the last one stays, in each context, for each two ports, and with each
rest. -/
def Signature.Cell.putPut (v w : Port Γ τ) (d : Diagram S Γ Qs) :
    Diagram.Derivation cell.rules (cell.put v (cell.put w d)) (cell.put w d) :=
  let each := Diagram.restOne (Γ := Γ) (Δ := []) d
  let a₀ : PortMap Γ [τ, τ] := .cons v (.cons w .nil)
  let ξ₁ : PortMap Γ Γ := PortMap.weaken [] (PortMap.id Γ)
  Diagram.Derivation.trans (R := cell.rules)
    (Diagram.Derivation.symm
      (.agree
        (cell.inlinePut (Boundary.only Γ) each (PortMap.id Γ) a₀ .here
          (cell.put (.there .here) (.exitOne .nil))
          (cell.inlinePut (Boundary.only Γ) each ξ₁ (a₀.lift []) (.there .here) (.exitOne .nil)
            (Diagram.renameAgree d _
              ((PortMap.weakenNil ξ₁).trans (PortMap.weakenNil (PortMap.id Γ))))))))
    (Diagram.Derivation.trans (R := cell.rules)
      (Diagram.Derivation.inline (Boundary.only Γ) each (Rules.Map.inl _ _)
        (Diagram.Derivation.rule (R := cell.rules) (Sum.inr Diagram.GlobalState.putPut))
        (PortMap.id Γ) a₀)
      (.agree
        (cell.inlinePut (Boundary.only Γ) each (PortMap.id Γ) a₀ (.there .here) (.exitOne .nil)
          (Diagram.renameAgree d _ (PortMap.weakenNil (PortMap.id Γ))))))

/-- A read and then a write of its value does nothing, in each context and with each rest. -/
def Signature.Cell.getPut (d : Diagram S Γ Qs) :
    Diagram.Derivation cell.rules
      (cell.get (cell.put .here (Diagram.rename (PortMap.weaken [τ] (PortMap.id Γ)) d))) d :=
  let each := Diagram.restOne (Γ := Γ) (Δ := []) d
  let ξ₁ : PortMap (τ :: Γ) Γ := PortMap.weaken [τ] (PortMap.id Γ)
  let a₁ : PortMap (τ :: Γ) [τ] := PortMap.lift [τ] (All.nil (P := Port Γ))
  Diagram.Derivation.trans (R := cell.rules)
    (Diagram.Derivation.symm
      (.agree
        (cell.inlineGet (Boundary.only Γ) each (PortMap.id Γ) .nil
          (cell.put .here (.exitOne .nil))
          (cell.inlinePut (Boundary.only Γ) each ξ₁ a₁ .here (.exitOne .nil)
            (Diagram.Agreement.renamePorts d (PortMap.weakenNil ξ₁))))))
    (Diagram.Derivation.trans (R := cell.rules)
      (Diagram.Derivation.inline (Boundary.only Γ) each (Rules.Map.inl _ _)
        (Diagram.Derivation.rule (R := cell.rules) (Sum.inr Diagram.GlobalState.getPut))
        (PortMap.id Γ) .nil)
      (.agree (Diagram.renameId d)))

/-- A write and then a read gives the written value, in each context, for each port, and with
each rest: the rest has the written port at its first port. -/
def Signature.Cell.putGet (v : Port Γ τ) (d : Diagram S (τ :: Γ) Qs) :
    Diagram.Derivation cell.rules (cell.put v (cell.get d))
      (cell.put v (Diagram.rename (.cons v (PortMap.id Γ)) d)) :=
  let each := Diagram.restOne (Γ := Γ) (Δ := [τ]) d
  let a₀ : PortMap Γ [τ] := .cons v .nil
  let ξ₁ : PortMap Γ Γ := PortMap.weaken [] (PortMap.id Γ)
  Diagram.Derivation.trans (R := cell.rules)
    (Diagram.Derivation.symm
      (.agree
        (cell.inlinePut (Boundary.only Γ) each (PortMap.id Γ) a₀ .here
          (cell.get (.exitOne (.cons .here .nil)))
          (cell.inlineGet (Boundary.only Γ) each ξ₁ (a₀.lift []) (.exitOne (.cons .here .nil))
            (Diagram.renameAgree d _
              ((Identity.cong
                  (fun (ζ : PortMap Γ Γ) =>
                    (All.cons (P := Port (τ :: Γ)) Elem.here (PortMap.weaken [τ] ζ) :
                      PortMap (τ :: Γ) (τ :: Γ)))
                  (PortMap.weakenNil (PortMap.id Γ))).trans
                (PortMap.liftId [τ] Γ)))))))
    (Diagram.Derivation.trans (R := cell.rules)
      (Diagram.Derivation.inline (Boundary.only Γ) each (Rules.Map.inl _ _)
        (Diagram.Derivation.rule (R := cell.rules) (Sum.inr Diagram.GlobalState.putGet))
        (PortMap.id Γ) a₀)
      (.agree
        (cell.inlinePut (Boundary.only Γ) each (PortMap.id Γ) a₀ .here
          (.exitOne (.cons .here .nil))
          (Diagram.Agreement.renamePorts d
            (Identity.cong (All.cons v) (PortMap.weakenNil (PortMap.id Γ)))))))

end Laws

section Sound

variable (cell : S.Cell τ) {α : Type}

/-- The cell as a morphism from the interface of a cell to the request interface, for each
family of values. A read is the call of the read with no operand, and its response gives the
value. A write is the call of the write with the value. -/
def Signature.Cell.hom : Hom (Container.cell (X τ)) (S.interface X) where
  shape
    | .get => ⟨cell.read, Identity.transport (All X) cell.readInput .nil⟩
    | .put a => ⟨cell.write, Identity.transport (All X) cell.writeInput (.cons a .nil)⟩
  position
    | .get => fun r => (Boundary.valuesAt cell.readOutput r).head
    | .put _ => fun _ => ⟨⟩

variable (stop : Free (S.interface X) α) (count : Nat)

/-- The computation of a typed read is the call of the cell, and then the rest with the
value. -/
def Signature.Cell.getRun {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S (τ :: Γ) Qs)
    (env : All X Γ) (k : Qs.At X → Free (S.interface X) α) :
    Free.Agreement ((cell.get d).run stop count env k)
      ((cell.hom.toImpl .get).bind fun a => d.run stop count (.cons a env) k) :=
  (Free.Agreement.ofIdentity
      (Identity.cong
        (fun args => Free.request (C := S.interface X) ⟨cell.read, args⟩ fun r =>
          ((Diagram.oneAt cell.readOutput d) r.1).run stop count (r.2.append env) k)
        (PortMap.selectTransport cell.readInput .nil env))).trans
    (Free.Agreement.request (C := S.interface X)
      (shape := ⟨cell.read, Identity.transport (All X) cell.readInput .nil⟩) fun r =>
      Free.Agreement.ofIdentity
        ((Diagram.oneAtRun stop count cell.readOutput d env k r).trans
          (Identity.cong (fun v => d.run stop count v k)
            (All.appendOne (Boundary.valuesAt cell.readOutput r) env))))

/-- The computation of a typed write is the call of the cell at the value of the port, and
then the rest. -/
def Signature.Cell.putRun {Γ : List Ty} {Qs : Exits Ty} (v : Port Γ τ) (d : Diagram S Γ Qs)
    (env : All X Γ) (k : Qs.At X → Free (S.interface X) α) :
    Free.Agreement ((cell.put v d).run stop count env k)
      ((cell.hom.toImpl (.put (env.lookup v))).bind fun _ => d.run stop count env k) :=
  (Free.Agreement.ofIdentity
      (Identity.cong
        (fun args => Free.request (C := S.interface X) ⟨cell.write, args⟩ fun r =>
          ((Diagram.oneAt (Δ := []) cell.writeOutput d) r.1).run stop count (r.2.append env) k)
        (PortMap.selectTransport cell.writeInput (.cons v .nil) env))).trans
    (Free.Agreement.request (C := S.interface X)
      (shape :=
        ⟨cell.write, Identity.transport (All X) cell.writeInput (.cons (env.lookup v) .nil)⟩)
      fun r =>
      Free.Agreement.ofIdentity
        ((Diagram.oneAtRun stop count (Δ := []) cell.writeOutput d env k r).trans
          (Identity.cong (fun (v : All X []) => d.run stop count (v.append env) k)
            (All.nilEta (Boundary.valuesAt cell.writeOutput r)))))

/-- The two sides of each equation of global state have one run on a machine that is, at the
calls of the cell, the machine of a cell along a lawful lens of the runtime. Each equation is
the equation of the machine of a cell, moved along the lens. -/
def Diagram.GlobalState.sound (m : Machine (S.interface X) R E)
    {ℓ : Hom (state R) (state (X τ))} (law : ℓ.Lawful)
    (same : Homotopy (m.impl cell.hom.toImpl) ((Machine.cell (X τ) E).along ℓ)) :
    {Γ : List Ty} → {Qs : Exits Ty} → {d e : Diagram S Γ Qs} → Diagram.GlobalState cell d e →
    (env : All X Γ) → (k : Qs.At X → Free (S.interface X) α) → (s : R) →
    m.run (d.run stop count env k) s ≡ m.run (e.run stop count env k) s
  | _, _, _, _, .getGet, env, k, s =>
      (Machine.runCongr
          ((cell.getRun stop count _ env k).trans
            (Free.Agreement.bind (.refl _) fun a => cell.getRun stop count _ (.cons a env) k))
          (Homotopy.refl m) s).trans
        ((Machine.alongCongr law (Machine.cell (X τ) E) cell.hom.toImpl m same
            (Container.cell.getGet (X τ) E (fun x y => .pure (y, x)))
            (fun (b : X τ × X τ) =>
              k ⟨_, .here, Boundary.only [τ, τ], .cons b.1 (.cons b.2 .nil)⟩) s).trans
          (Machine.runCongr
            (cell.getRun stop count (.exitOne (.cons .here (.cons .here .nil))) env k)
            (Homotopy.refl m) s).symm)
  | _, _, _, _, .getDiscard, env, k, s =>
      (Machine.runCongr (cell.getRun stop count (.exitOne .nil) env k) (Homotopy.refl m) s).trans
        (Machine.alongCongr law (Machine.cell (X τ) E) cell.hom.toImpl m same
          (Container.cell.getDiscard (X τ) E (.pure ()))
          (fun (_ : Unit) => (Diagram.exitOne (S := S) .nil).run stop count env k) s)
  | _, _, _, _, .putPut, env, k, s =>
      (Machine.runCongr
          ((cell.putRun stop count .here _ env k).trans
            (Free.Agreement.bind (.refl _) fun _ =>
              cell.putRun stop count (.there .here) (.exitOne .nil) env k))
          (Homotopy.refl m) s).trans
        ((Machine.alongCongr law (Machine.cell (X τ) E) cell.hom.toImpl m same
            (Container.cell.putPut (X τ) E (env.lookup .here) (env.lookup (.there .here))
              (.pure ()))
            (fun (_ : Unit) => (Diagram.exitOne (S := S) .nil).run stop count env k) s).trans
          (Machine.runCongr (cell.putRun stop count (.there .here) (.exitOne .nil) env k)
            (Homotopy.refl m) s).symm)
  | _, _, _, _, .getPut, env, k, s =>
      (Machine.runCongr
          ((cell.getRun stop count _ env k).trans
            (Free.Agreement.bind (.refl _) fun a =>
              cell.putRun stop count .here (.exitOne .nil) (.cons a env) k))
          (Homotopy.refl m) s).trans
        (Machine.alongCongr law (Machine.cell (X τ) E) cell.hom.toImpl m same
          (Container.cell.getPut (X τ) E (.pure ()))
          (fun (_ : Unit) => (Diagram.exitOne (S := S) .nil).run stop count env k) s)
  | _, _, _, _, .putGet, env, k, s =>
      (Machine.runCongr
          ((cell.putRun stop count .here _ env k).trans
            (Free.Agreement.bind (.refl _) fun _ => cell.getRun stop count _ env k))
          (Homotopy.refl m) s).trans
        ((Machine.alongCongr law (Machine.cell (X τ) E) cell.hom.toImpl m same
            (Container.cell.putGet (X τ) E (env.lookup .here) .pure)
            (fun (b : X τ) => k ⟨_, .here, Boundary.only [τ], .cons b .nil⟩) s).trans
          (Machine.runCongr
            (cell.putRun stop count .here (.exitOne (.cons .here .nil)) env k)
            (Homotopy.refl m) s).symm)

/-- The equation set of global state holds on each machine that is, at the calls of the cell,
the machine of a cell along a lawful lens of the runtime. -/
def Rules.Sound.globalState (m : Machine (S.interface X) R E)
    {ℓ : Hom (state R) (state (X τ))} (law : ℓ.Lawful)
    (same : Homotopy (m.impl cell.hom.toImpl) ((Machine.cell (X τ) E).along ℓ)) :
    (Rules.globalState cell).Sound (α := α) m.congruence :=
  ⟨fun stop count _ _ _ _ r env k s =>
      Diagram.GlobalState.sound cell stop count m law same r env k s,
    fun _ _ => fun r => nomatch r⟩

end Sound

end Cell

end Draft
