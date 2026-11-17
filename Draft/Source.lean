import Draft.Diagram

/-! Source diagrams of the fragment with fixed occurrences.

A diagram of the fragment is one sequence of steps and one exit. The output boundary of each
step has one case: the type of its cases has a center, and each case is identical to the
center. The evidence is a function of the diagram, by a recursion on it. The action of a port
map keeps the fragment. The operations of a diagram of the fragment are a list, in the order of
its steps.

The dependency graph of a diagram of the fragment has no names. A value is its history: an
input of the diagram, or an output port of the call that made it. A call has the histories of
its operands and the effectful call before it, which is the state edge of the graph. The graph
is the list of the occurrences of the steps of the diagram: each step is a call at the
histories of its context, and its output ports have that call as their history. The container
of the graph has a shape for each occurrence and a position for each operand. The occurrences
of a diagram with renamed ports are the occurrences of the diagram at the selected histories.

The graph is a specification of the runs of its steps. The runtime has the list of the
remaining occurrences and the list of the done occurrences. A run has the number of an
occurrence in the list of the remaining occurrences. It is admitted when the call of each
operand is done, and the effectful call before it is done. The response has the remaining list
without the occurrence and the done list with it. A word of runs is an admissible order when it
has evidence of this specification, with no remaining occurrence at its end. Each occurrence
thus has one run.

Two calls of a pure operation at the same ports are one call in the merged diagram. The merge
goes through the steps one time, from the first step. It has the list of the available calls:
the calls of pure operations in the steps before, each with its ports and its output ports in
the context of the merged diagram, and a port map from the context of the source diagram to
that context. A step whose operation and ports are those of an available call is not a step of
the merged diagram: the rest has the output ports of the available call. Each other step is a
step of the merged diagram, and its call is available to the rest when its operation is pure.
The decision uses the identity of two operations and the identity of two ports.

The merged diagram has a derivation from the source diagram, in each rule set that has the
interchange rule and the copy rule. The proof is one recursion on the diagram, for a context of
diagrams that absorbs each available call: in the context, a step at the ports of the call is
the rest with the output ports of the call. The context under a step absorbs the call of that
step by the copy rule. It absorbs each earlier call by one interchange and the absorption of
the context before. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

variable {Ty : Type} {S : Signature Ty}

/-- The evidence that a diagram is one sequence of steps and one exit. A step has the center
of the cases of its output boundary, the identity of each case with the center, and the
evidence of its rest at the center. -/
def Diagram.Straight : {Γ : List Ty} → {Qs : Exits Ty} → Diagram S Γ Qs → Type
  | _, _, .exit _ => Unit
  | _, _, .step call rest =>
      (center : (S.output call.1).Case) ×
        (((c : (S.output call.1).Case) → center ≡ c) × Diagram.Straight (rest center))
  | _, _, .seq _ _ => Empty

/-- The action of a port map keeps the fragment. -/
def Diagram.Straight.rename : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) → d.Straight → (d.rename ρ).Straight
  | _, _, _, _, .exit _, _ => ()
  | _, _, _, ρ, .step _ rest, h => ⟨h.1, h.2.1, rename (ρ.lift h.1.1) (rest h.1) h.2.2⟩
  | _, _, _, _, .seq _ _, h => nomatch h

/-- The operations of a diagram of the fragment, in the order of its steps. -/
def Diagram.ops : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) → d.Straight →
    List S.Op
  | _, _, .exit _, _ => []
  | _, _, .step call rest, h => call.1 :: Diagram.ops (rest h.1) h.2.2
  | _, _, .seq _ _, _ => []

/-! The dependency graph. -/

mutual

/-- The history of a value: an input of the source diagram, or an output port of a call at an
output case. -/
inductive History (S : Signature Ty) (Γ₀ : List Ty) : Ty → Type where
  | input {t : Ty} (p : Port Γ₀ t) : History S Γ₀ t
  | output {t : Ty} {o : S.Op} (call : Call S Γ₀ o) (c : (S.output o).Case) (q : Port c.1 t) :
      History S Γ₀ t

/-- A call of an operation: the histories of its operands, and the effectful call before it. A
pure call has no effectful call before it. -/
inductive Call (S : Signature Ty) (Γ₀ : List Ty) : S.Op → Type where
  | mk {o : S.Op} (args : All (History S Γ₀) (S.input o)) (before : Option (Effect S Γ₀)) :
      Call S Γ₀ o

/-- An effectful call. -/
inductive Effect (S : Signature Ty) (Γ₀ : List Ty) : Type where
  | after {o : S.Op} (call : Call S Γ₀ o) : Effect S Γ₀

end

variable {Γ₀ : List Ty}

/-- An occurrence of a step: its operation with its call. -/
abbrev Signature.Occurrence (S : Signature Ty) (Γ₀ : List Ty) : Type :=
  (o : S.Op) × Call S Γ₀ o

/-- The histories of the operands of a call. -/
def Call.args {o : S.Op} : Call S Γ₀ o → All (History S Γ₀) (S.input o)
  | .mk args _ => args

/-- The effectful call before a call. -/
def Call.before {o : S.Op} : Call S Γ₀ o → Option (Effect S Γ₀)
  | .mk _ before => before

/-- The effectful call before a step of a kind. A pure step has none. -/
def Kind.before {N : Type} : Kind → Option N → Option N
  | .pure, _ => none
  | .effectful, last => last

/-- The last effectful call after a step of a kind. -/
def Kind.last {N : Type} : Kind → Option N → N → Option N
  | .pure, last, _ => last
  | .effectful, _, n => some n

/-- The effectful call before the second of two steps does not change when the first step moves
past it: one of the two kinds is the pure kind. -/
def Kind.beforeSecond {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (x : N) → Kind.before l (Kind.last k last x) ≡ Kind.before l last
  | .pure, .pure, _, _, _ => .refl
  | .pure, .effectful, _, _, _ => .refl
  | .effectful, .pure, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _ => nomatch e

/-- The same for the first of the two steps. -/
def Kind.beforeFirst {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (y : N) → Kind.before k (Kind.last l last y) ≡ Kind.before k last
  | .pure, .pure, _, _, _ => .refl
  | .pure, .effectful, _, _, _ => .refl
  | .effectful, .pure, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _ => nomatch e

/-- The last effectful call after two steps does not change with their order, when one of the
two kinds is the pure kind. -/
def Kind.lastSwap {N : Type} : (k l : Kind) → ((k ≡ .pure) ⊕ (l ≡ .pure)) →
    (last : Option N) → (x y : N) →
    Kind.last l (Kind.last k last x) y ≡ Kind.last k (Kind.last l last y) x
  | .pure, .pure, _, _, _, _ => .refl
  | .pure, .effectful, _, _, _, _ => .refl
  | .effectful, .pure, _, _, _, _ => .refl
  | .effectful, .effectful, .inl e, _, _, _ => nomatch e
  | .effectful, .effectful, .inr e, _, _, _ => nomatch e

/-- The histories of a context after a call at an output case: the output ports of the call,
and then the histories of the context before it. -/
def Call.outputs {o : S.Op} (call : Call S Γ₀ o) (c : (S.output o).Case) {Γ : List Ty}
    (env : All (History S Γ₀) Γ) : All (History S Γ₀) (c.1 ++ Γ) :=
  (All.tabulate c.1 fun _ q => History.output call c q).append env

/-- The call of a step at the histories of its context, after the last effectful call. -/
def Call.at (o : S.Op) {Γ : List Ty} (args : PortMap Γ (S.input o)) (env : All (History S Γ₀) Γ)
    (last : Option (Effect S Γ₀)) : Call S Γ₀ o :=
  .mk (env.select args) (Kind.before (S.kind o) last)

/-- The last effectful call after a call. -/
def Call.next {o : S.Op} (call : Call S Γ₀ o) (last : Option (Effect S Γ₀)) :
    Option (Effect S Γ₀) :=
  Kind.last (S.kind o) last (.after call)

/-- The occurrences of the steps of a diagram of the fragment at the histories of its context,
after the last effectful call. Each step is a call at the histories of its context, and its
output ports have that call as their history. -/
def Diagram.occurrences : {Γ : List Ty} → {Qs : Exits Ty} → (d : Diagram S Γ Qs) →
    d.Straight → All (History S Γ₀) Γ → Option (Effect S Γ₀) → List (S.Occurrence Γ₀)
  | _, _, .exit _, _, _, _ => []
  | _, _, .step call rest, h, env, last =>
      ⟨call.1, Call.at call.1 call.2 env last⟩ ::
        Diagram.occurrences (rest h.1) h.2.2
          ((Call.at call.1 call.2 env last).outputs h.1 env)
          ((Call.at call.1 call.2 env last).next last)
  | _, _, .seq _ _, _, _, _ => []

/-- The histories of the inputs of a source diagram. -/
def Signature.inputs (S : Signature Ty) (Γ₀ : List Ty) : All (History S Γ₀) Γ₀ :=
  All.tabulate Γ₀ fun _ p => .input p

/-- The dependency graph of a diagram of the fragment: the occurrences of its steps at the
histories of its inputs. -/
def Diagram.graph {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs) (h : d.Straight) :
    List (S.Occurrence Γ) :=
  d.occurrences h (S.inputs Γ) none

/-- The occurrences of a diagram with renamed ports are the occurrences of the diagram at the
selected histories. -/
def Diagram.occurrencesRename : {Γ Δ : List Ty} → {Qs : Exits Ty} → (ρ : PortMap Γ Δ) →
    (d : Diagram S Δ Qs) → (h : d.Straight) → (env : All (History S Γ₀) Γ) →
    (last : Option (Effect S Γ₀)) →
    (d.rename ρ).occurrences (Diagram.Straight.rename ρ d h) env last ≡
      d.occurrences h (env.select ρ) last
  | _, _, _, _, .exit _, _, _, _ => .refl
  | _, _, _, ρ, .step call rest, h, env, last =>
      (Identity.cong
          (fun tail =>
            (⟨call.1, Call.at call.1 (ρ.select call.2) env last⟩ : S.Occurrence Γ₀) :: tail)
          ((Diagram.occurrencesRename (ρ.lift h.1.1) (rest h.1) h.2.2
              ((Call.at call.1 (ρ.select call.2) env last).outputs h.1 env)
              ((Call.at call.1 (ρ.select call.2) env last).next last)).trans
            (Identity.cong
              (fun vals =>
                Diagram.occurrences (rest h.1) h.2.2 vals
                  ((Call.at call.1 (ρ.select call.2) env last).next last))
              (PortMap.selectLift _ env ρ)))).trans
        (Identity.cong
          (fun (args : All (History S Γ₀) (S.input call.1)) =>
            ((⟨call.1, .mk args (Kind.before (S.kind call.1) last)⟩ : S.Occurrence Γ₀) ::
              Diagram.occurrences (rest h.1) h.2.2
                ((Call.mk args (Kind.before (S.kind call.1) last)).outputs h.1
                  (env.select ρ))
                ((Call.mk args (Kind.before (S.kind call.1) last)).next last)))
          (All.selectSelect env ρ call.2))
  | _, _, _, _, .seq _ _, h, _, _ => nomatch h

/-- The occurrences of the rest of a step at a case are the occurrences at the center of the
cases. -/
def Diagram.occurrencesCase {o : S.Op} {Γ : List Ty} {Qs : Exits Ty}
    (rest : (c : (S.output o).Case) → Diagram S (c.1 ++ Γ) Qs) {center c : (S.output o).Case}
    (p : center ≡ c) (tail : (rest center).Straight) (call : Call S Γ₀ o)
    (env : All (History S Γ₀) Γ) (last : Option (Effect S Γ₀)) :
    (rest center).occurrences tail (call.outputs center env) last ≡
      (rest c).occurrences (Identity.transport (fun c => (rest c).Straight) p tail)
        (call.outputs c env) last :=
  Identity.ind
    (fun c p =>
      (rest center).occurrences tail (call.outputs center env) last ≡
        (rest c).occurrences (Identity.transport (fun c => (rest c).Straight) p tail)
          (call.outputs c env) last)
    .refl p

/-- The container of a dependency graph: a shape for each occurrence, and a position for each
operand. -/
def Signature.incidence (G : List (S.Occurrence Γ₀)) : Container where
  Shape := (a : S.Occurrence Γ₀) × Elem a G
  Pos s := (t : Ty) × Port (S.input s.1.1) t

/-- The producer of each operand: its history. -/
def Signature.producer (G : List (S.Occurrence Γ₀)) (s : (Signature.incidence G).Shape)
    (p : (Signature.incidence G).Pos s) : History S Γ₀ p.1 :=
  s.1.2.args.lookup p.2

/-! The specification of the runs. -/

/-- The element at a number in a list, with the other elements in their order. -/
def takeAt {α : Type} : Nat → List α → Option (α × List α)
  | _, [] => none
  | 0, a :: rest => some (a, rest)
  | k + 1, a :: rest => (takeAt k rest).map fun found => (found.1, a :: found.2)

/-- A history is produced for a list of done occurrences: it is an input, or its call is in the
list. -/
def History.Produced (done : List (S.Occurrence Γ₀)) : {t : Ty} → History S Γ₀ t → Type
  | _, .input _ => Unit
  | _, .output (o := o) call _ _ => Elem (⟨o, call⟩ : S.Occurrence Γ₀) done

/-- The effectful call before a call is done, or the call has none. -/
def Effect.Produced (done : List (S.Occurrence Γ₀)) : Option (Effect S Γ₀) → Type
  | none => Unit
  | some (.after (o := o) call) => Elem (⟨o, call⟩ : S.Occurrence Γ₀) done

/-- The interface of the runs: a call has the number of an occurrence in the list of the
remaining occurrences. -/
def runs : Container := ⟨Nat, fun _ => Unit⟩

/-- The runtime of the runs of a dependency graph: the remaining occurrences, and the done
occurrences. -/
abbrev Signature.Progress (S : Signature Ty) (Γ₀ : List Ty) : Type :=
  List (S.Occurrence Γ₀) × List (S.Occurrence Γ₀)

/-- The specification of the runs of a dependency graph. A run is admitted when its number has
an occurrence in the list of the remaining occurrences, the call of each operand of that
occurrence is done, and the effectful call before it is done. The response has the remaining
list without the occurrence and the done list with it. -/
def Signature.admissible (S : Signature Ty) (Γ₀ : List Ty) :
    DepPoly.{0, 0, 0, 0} (runs.runtime (S.Progress Γ₀) Empty) where
  Pre a :=
    (found : S.Occurrence Γ₀ × List (S.Occurrence Γ₀)) ×
      ((takeAt a.1 a.2.1 ≡ some found) ×
        (((t : Ty) → (p : Port (S.input found.1.1) t) →
            History.Produced a.2.2 (found.1.2.args.lookup p)) ×
          Effect.Produced a.2.2 found.1.2.before))
  Post a pre := fun
    | .inl _ => Empty
    | .inr next => next.2 ≡ (pre.1.2, pre.1.1 :: a.2.2)

/-- The condition at the end of a word: no occurrence remains. -/
def Signature.Finished (S : Signature Ty) (Γ₀ : List Ty) :
    Empty ⊕ (Unit × S.Progress Γ₀) → Type
  | .inl _ => Empty
  | .inr out => out.2.1 ≡ []

/-- The word of a list of numbers: one run for each number. -/
def word : List Nat → Free runs Unit
  | [] => .pure ()
  | k :: rest => .request k fun _ => word rest

/-- The evidence of one run and then the rest: a witness of the precondition, and the evidence
of the rest from the next runtime. -/
def Signature.ran {Q : Empty ⊕ (Unit × S.Progress Γ₀) → Type} (k : Nat)
    (state : S.Progress Γ₀) {rest : Free runs Unit}
    (pre : (S.admissible Γ₀).Pre (k, state))
    (next : FreeDep (S.admissible Γ₀) Q
      (rest.thread (E := Empty) (pre.1.2, pre.1.1 :: state.2))) :
    FreeDep (S.admissible Γ₀) Q ((Free.request (C := runs) k fun _ => rest).thread state) :=
  FreeDep.request (r := S.admissible Γ₀) (shape := (k, state))
    (next := Sum.elim (fun stopped => .pure (.inl stopped))
      (fun (b : Unit × S.Progress Γ₀) => rest.thread b.2))
    pre
    fun b =>
      Sum.casesOn
        (motive := fun b => (S.admissible Γ₀).Post (k, state) pre b →
          FreeDep (S.admissible Γ₀) Q
            (Sum.elim (fun stopped => Free.pure (.inl stopped))
              (fun (b : Unit × S.Progress Γ₀) => rest.thread b.2) b))
        b (fun _ post => post.elim)
        (fun _ post =>
          Identity.transport (fun st => FreeDep (S.admissible Γ₀) Q (rest.thread st))
            post.symm next)

/-! The merge of the equal calls. -/

/-- The identity of a kind with the pure kind, when the kind is the pure kind. -/
def Kind.isPure : (k : Kind) → Option (k ≡ .pure)
  | .pure => some .refl
  | .effectful => none

/-- An available call: a call of a pure operation in the steps before a point, with its ports,
the one case of its output boundary, and its output ports. -/
structure Available (S : Signature Ty) (Γ : List Ty) where
  op : S.Op
  pure : S.kind op ≡ .pure
  args : PortMap Γ (S.input op)
  center : (S.output op).Case
  only : (c : (S.output op).Case) → center ≡ c
  outs : PortMap Γ center.1

/-- The data of a call that a later step can use: an operation, its ports, a case of its output
boundary, and the output ports of that case. -/
abbrev Used (S : Signature Ty) (Γ : List Ty) : Type :=
  (o : S.Op) × (PortMap Γ (S.input o) × ((c : (S.output o).Case) × PortMap Γ c.1))

namespace Available

variable {Γ : List Ty}

/-- The data of an available call. -/
def used (e : Available S Γ) : Used S Γ := ⟨e.op, e.args, e.center, e.outs⟩

/-- An available call in a context with more ports. -/
def weaken (Ξ : List Ty) (e : Available S Γ) : Available S (Ξ ++ Γ) :=
  ⟨e.op, e.pure, e.args.weaken Ξ, e.center, e.only, PortMap.weaken Ξ e.outs⟩

/-- The call of a step with a pure operation, in the context after the step. -/
def ofStep (f : S.Op) (pure : S.kind f ≡ .pure) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c) :
    Available S (center.1 ++ Γ) :=
  ⟨f, pure, args.weaken center.1, center, only,
    All.tabulate (P := Port (center.1 ++ Γ)) center.1 fun _ i => i.left⟩

/-- The available calls after a step: the call of the step when its operation is pure, and
then the calls before the step. -/
def after (table : List (Available S Γ)) (f : S.Op) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c) :
    List (Available S (center.1 ++ Γ)) :=
  Option.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ)))
    (Kind.isPure (S.kind f))
    (table.map (weaken center.1))
    (fun pure => ofStep f pure args center only :: table.map (weaken center.1))

/-- The case and the output ports of an available call, when it is a call of the operation at
the ports. -/
def use [DecEq S.Op] (e : Available S Γ) (f : S.Op) (args : PortMap Γ (S.input f)) :
    Option ((c : (S.output f).Case) × ((outs : PortMap Γ c.1) × (e.used ≡ ⟨f, args, c, outs⟩))) :=
  match decideEq e.op f with
  | .no _ => none
  | .yes sameOp =>
      Identity.ind
        (fun (f : S.Op) _ => (args : PortMap Γ (S.input f)) →
          Option ((c : (S.output f).Case) ×
            ((outs : PortMap Γ c.1) × (e.used ≡ ⟨f, args, c, outs⟩))))
        (fun args =>
          match All.decide (fun _ => Elem.decide) e.args args with
          | .no _ => none
          | .yes samePorts =>
              Identity.ind
                (fun (args : PortMap Γ (S.input e.op)) _ =>
                  Option ((c : (S.output e.op).Case) ×
                    ((outs : PortMap Γ c.1) × (e.used ≡ ⟨e.op, args, c, outs⟩))))
                (some ⟨e.center, e.outs, .refl⟩) samePorts)
        sameOp args

/-- An available call of a list that is a call of an operation at given ports, with its case
and its output ports. -/
structure Found (table : List (Available S Γ)) (f : S.Op) (args : PortMap Γ (S.input f)) where
  entry : Available S Γ
  mem : Elem entry table
  center : (S.output f).Case
  outs : PortMap Γ center.1
  same : entry.used ≡ ⟨f, args, center, outs⟩

/-- The first available call of a list that is a call of the operation at the ports. -/
def find [DecEq S.Op] (f : S.Op) (args : PortMap Γ (S.input f)) :
    (table : List (Available S Γ)) → Option (Found table f args)
  | [] => none
  | e :: rest =>
      Option.casesOn (motive := fun _ => Option (Found (e :: rest) f args)) (e.use f args)
        ((find f args rest).map fun found =>
          ⟨found.entry, .there found.mem, found.center, found.outs, found.same⟩)
        (fun m => some ⟨e, .here, m.1, m.2.1, m.2.2⟩)

end Available

/-- The step with one output case, with a diagram at the center of the cases as its rest. -/
def Diagram.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op) (args : PortMap Γ (S.input f))
    (center : (S.output f).Case) (only : (c : (S.output f).Case) → center ≡ c)
    (D : Diagram S (center.1 ++ Γ) Qs) : Diagram S Γ Qs :=
  .step ⟨f, args⟩ fun c =>
    Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) (only c) D

/-- The merge of a diagram of the fragment at a list of available calls and a port map to the
context of the merged diagram. -/
def Diagram.mergeWith [DecEq S.Op] : {Γ Δ : List Ty} → {Qs : Exits Ty} →
    List (Available S Γ) → PortMap Γ Δ → (d : Diagram S Δ Qs) → d.Straight → Diagram S Γ Qs
  | _, _, _, _, ρ, .exit out, _ => .exit (out.select ρ)
  | Γ, _, Qs, table, ρ, .step call rest, h =>
      Option.casesOn (motive := fun _ => Diagram S Γ Qs)
        (Available.find call.1 (ρ.select call.2) table)
        (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
          (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
            (ρ.lift h.1.1) (rest h.1) h.2.2))
        (fun found =>
          Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
            (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2))
  | _, _, _, _, _, .seq _ _, h => nomatch h

/-- The merge of the equal calls of a diagram of the fragment. -/
def Diagram.merge [DecEq S.Op] {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) : Diagram S Γ Qs :=
  Diagram.mergeWith [] (PortMap.id Γ) d h

/-! The derivation of the merged diagram. -/

variable {R : Rules S}

/-- A context of diagrams absorbs the data of a call: in the context, a step of the operation
at the ports is the rest at the case, with the output ports in the place of the output ports
of the step. -/
def Absorbed (R : Rules S) {Γ Γ₀ : List Ty} {Qs : Exits Ty}
    (K : Diagram S Γ Qs → Diagram S Γ₀ Qs) (k : Used S Γ) : Type :=
  (D : (c : (S.output k.1).Case) → Diagram S (c.1 ++ Γ) Qs) →
    Diagram.Derivation R (K (.step ⟨k.1, k.2.1⟩ D))
      (K (Diagram.rename (k.2.2.2.append (PortMap.id Γ)) (D k.2.2.1)))

/-- The derivations are a congruence for the step with one output case. -/
def Diagram.Derivation.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op)
    (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
    (only : (c : (S.output f).Case) → center ≡ c) {D D' : Diagram S (center.1 ++ Γ) Qs}
    (der : Diagram.Derivation R D D') :
    Diagram.Derivation R (Diagram.under f args center only D)
      (Diagram.under f args center only D') :=
  .step ⟨f, args⟩ fun c =>
    Identity.ind
      (fun (c : (S.output f).Case) (p : center ≡ c) =>
        Diagram.Derivation R
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p D)
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p D'))
      der (only c)

/-- A step with one output case agrees with the step that has the diagram of the center as its
rest. -/
def Diagram.Agreement.under {Γ : List Ty} {Qs : Exits Ty} (f : S.Op)
    (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
    (only : (c : (S.output f).Case) → center ≡ c)
    (rest : (c : (S.output f).Case) → Diagram S (c.1 ++ Γ) Qs) :
    Diagram.Agreement (.step ⟨f, args⟩ rest) (Diagram.under f args center only (rest center)) :=
  .step ⟨f, args⟩ fun c =>
    Identity.ind
      (fun (c : (S.output f).Case) (p : center ≡ c) =>
        Diagram.Agreement (rest c)
          (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
            (rest center)))
      (Diagram.Agreement.refl _) (only c)

section

variable {Γ Γ₀ : List Ty} {Qs : Exits Ty} {K : Diagram S Γ Qs → Diagram S Γ₀ Qs}
  (cong : {D D' : Diagram S Γ Qs} → Diagram.Derivation R D D' →
    Diagram.Derivation R (K D) (K D'))
  (f : S.Op) (args : PortMap Γ (S.input f)) (center : (S.output f).Case)
  (only : (c : (S.output f).Case) → center ≡ c)

/-- The context under a step absorbs the call of the step, by the copy rule. -/
def Absorbed.ofStep (copy : Rules.Map (Rules.copy S) R) (pure : S.kind f ≡ .pure) :
    Absorbed R (fun D => K (Diagram.under f args center only D))
      (Available.ofStep f pure args center only).used :=
  fun D =>
    (cong (.agree (.step ⟨f, args⟩ fun ca =>
        Identity.ind
          (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
            Diagram.Agreement
              (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                (.step ⟨f, args.weaken center.1⟩ D))
              (.step ⟨f, args.weaken ca.1⟩ fun c' =>
                Identity.transport
                  (fun (c : (S.output f).Case) => Diagram S (c'.1 ++ (c.1 ++ Γ)) Qs) p (D c')))
          (Diagram.Agreement.refl _) (only ca)))).trans
      ((cong (.rule (copy.diagram (.copy f pure args fun ca c' =>
          Identity.transport
            (fun (c : (S.output f).Case) => Diagram S (c'.1 ++ (c.1 ++ Γ)) Qs) (only ca)
            (D c'))))).trans
        (cong (.agree (.step ⟨f, args⟩ fun ca =>
          Identity.ind
            (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
              Diagram.Agreement
                (Diagram.rename (PortMap.copy ca.1 Γ)
                  (Identity.transport
                    (fun (c : (S.output f).Case) => Diagram S (ca.1 ++ (c.1 ++ Γ)) Qs) p
                    (D ca)))
                (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                  (Diagram.rename (PortMap.copy center.1 Γ) (D center))))
            (Diagram.Agreement.refl _) (only ca)))))

/-- The ports of an available call under more ports, after the exchange with those ports. -/
def Available.underPorts (Ξ : List Ty) (e : Available S Γ) :
    (PortMap.lift Ξ (e.outs.append (PortMap.id Γ))).select (PortMap.exchange Ξ e.center.1 Γ) ≡
      (PortMap.weaken Ξ e.outs).append (PortMap.id (Ξ ++ Γ)) :=
  (Identity.cong
      (fun (m : PortMap (Ξ ++ Γ) (e.center.1 ++ Γ)) =>
        All.select
          ((All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left)).append m)
          (PortMap.exchange Ξ e.center.1 Γ))
      (All.mapAppend (fun (t : Ty) (i : Port Γ t) => (i.right Ξ : Port (Ξ ++ Γ) t)) e.outs
        (PortMap.id Γ))).trans
    ((PortMap.selectExchange (All.tabulate (P := Port (Ξ ++ Γ)) Ξ (fun _ i => i.left))
        (PortMap.weaken Ξ e.outs) (PortMap.weaken Ξ (PortMap.id Γ))).trans
      (Identity.cong (All.append (PortMap.weaken Ξ e.outs)) (PortMap.liftId Ξ Γ)))

/-- The context under a step absorbs each call that the context before absorbs: the step of the
call moves before the step of the context by one interchange. -/
def Absorbed.under (inter : Rules.Map (Rules.interchange S) R) (e : Available S Γ)
    (absorbed : Absorbed R K e.used) :
    Absorbed R (fun D => K (Diagram.under f args center only D)) (e.weaken center.1).used :=
  fun D =>
    (cong (.agree (.step ⟨f, args⟩ fun ca =>
        Identity.ind
          (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
            Diagram.Agreement
              (Identity.transport (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                (.step ⟨e.op, e.args.weaken center.1⟩ D))
              (.step ⟨e.op, e.args.weaken ca.1⟩ fun cb =>
                Identity.transport
                  (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) p (D cb)))
          (Diagram.Agreement.refl _) (only ca)))).trans
      ((cong (.rule (inter.diagram (.swap f e.op (.inr e.pure) args e.args fun ca cb =>
          Identity.transport
            (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) (only ca)
            (D cb))))).trans
        ((absorbed fun cb => .step ⟨f, args.weaken cb.1⟩ fun ca =>
            Diagram.rename (PortMap.exchange ca.1 cb.1 Γ)
              (Identity.transport
                (fun (c : (S.output f).Case) => Diagram S (cb.1 ++ (c.1 ++ Γ)) Qs) (only ca)
                (D cb))).trans
          (cong (.agree (.stepPorts f
            ((PortMap.selectWeaken e.outs (PortMap.id Γ) args).trans (PortMap.idSelect args))
            fun ca =>
              Identity.ind
                (fun (ca : (S.output f).Case) (p : center ≡ ca) =>
                  Diagram.Agreement
                    (Diagram.rename (PortMap.lift ca.1 (e.outs.append (PortMap.id Γ)))
                      (Diagram.rename (PortMap.exchange ca.1 e.center.1 Γ)
                        (Identity.transport
                          (fun (c : (S.output f).Case) =>
                            Diagram S (e.center.1 ++ (c.1 ++ Γ)) Qs) p (D e.center))))
                    (Identity.transport
                      (fun (c : (S.output f).Case) => Diagram S (c.1 ++ Γ) Qs) p
                      (Diagram.rename
                        ((PortMap.weaken center.1 e.outs).append (PortMap.id (center.1 ++ Γ)))
                        (D e.center))))
                (Diagram.renameCompose (D e.center) _ _ _ (e.underPorts center.1))
                (only ca))))))

/-- The context under a step absorbs each available call after the step. -/
def Absorbed.after (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) (table : List (Available S Γ))
    (absorbed : All (fun e => Absorbed R K e.used) table) :
    All (fun e => Absorbed R (fun D => K (Diagram.under f args center only D)) e.used)
      (Available.after table f args center only) :=
  Option.casesOn
    (motive := fun pure =>
      All (fun e => Absorbed R (fun D => K (Diagram.under f args center only D)) e.used)
        (Option.casesOn (motive := fun _ => List (Available S (center.1 ++ Γ))) pure
          (table.map (Available.weaken center.1))
          (fun pure =>
            Available.ofStep f pure args center only :: table.map (Available.weaken center.1))))
    (Kind.isPure (S.kind f))
    (All.image (Available.weaken center.1)
      (fun e a => Absorbed.under cong f args center only inter e a) absorbed)
    (fun pure =>
      .cons (Absorbed.ofStep cong f args center only copy pure)
        (All.image (Available.weaken center.1)
          (fun e a => Absorbed.under cong f args center only inter e a) absorbed))

end

/-- The merged diagram has a derivation from the diagram with the ports of the map, in each
context that absorbs each available call. -/
def Diagram.mergeWithDerivation [DecEq S.Op] (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) {Γ₀ : List Ty} :
    {Γ Δ : List Ty} → {Qs : Exits Ty} → (K : Diagram S Γ Qs → Diagram S Γ₀ Qs) →
    (cong : {D D' : Diagram S Γ Qs} → Diagram.Derivation R D D' →
      Diagram.Derivation R (K D) (K D')) →
    (table : List (Available S Γ)) → All (fun e => Absorbed R K e.used) table →
    (ρ : PortMap Γ Δ) → (d : Diagram S Δ Qs) → (h : d.Straight) →
    Diagram.Derivation R (K (Diagram.rename ρ d)) (K (Diagram.mergeWith table ρ d h))
  | _, _, _, _, _, _, _, _, .exit _, _ => .agree (Diagram.Agreement.refl _)
  | Γ, _, Qs, K, cong, table, absorbed, ρ, .step call rest, h =>
      Option.casesOn
        (motive := fun found =>
          Diagram.Derivation R
            (K (.step ⟨call.1, ρ.select call.2⟩ fun c => Diagram.rename (ρ.lift c.1) (rest c)))
            (K (Option.casesOn (motive := fun _ => Diagram S Γ Qs) found
              (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1
                (Diagram.mergeWith (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
                  (ρ.lift h.1.1) (rest h.1) h.2.2))
              (fun found =>
                Diagram.mergeWith table (found.outs.append ρ) (rest found.center)
                  (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center)
                    h.2.2)))))
        (Available.find call.1 (ρ.select call.2) table)
        ((cong (.agree (Diagram.Agreement.under call.1 (ρ.select call.2) h.1 h.2.1
            fun c => Diagram.rename (ρ.lift c.1) (rest c)))).trans
          (Diagram.mergeWithDerivation inter copy
            (fun D => K (Diagram.under call.1 (ρ.select call.2) h.1 h.2.1 D))
            (fun der => cong (der.under call.1 (ρ.select call.2) h.1 h.2.1))
            (Available.after table call.1 (ρ.select call.2) h.1 h.2.1)
            (Absorbed.after cong call.1 (ρ.select call.2) h.1 h.2.1 inter copy table absorbed)
            (ρ.lift h.1.1) (rest h.1) h.2.2))
        (fun found =>
          ((Identity.transport (Absorbed R K) found.same (absorbed.lookup found.mem))
              fun c => Diagram.rename (ρ.lift c.1) (rest c)).trans
            ((cong (.agree (Diagram.renameCompose (rest found.center) _ _ _
                ((PortMap.selectLift found.outs (PortMap.id Γ) ρ).trans
                  (Identity.cong (All.append found.outs) (PortMap.idSelect ρ)))))).trans
              (Diagram.mergeWithDerivation inter copy K cong table absorbed
                (found.outs.append ρ) (rest found.center)
                (Identity.transport (fun c => (rest c).Straight) (h.2.1 found.center) h.2.2))))
  | _, _, _, _, _, _, _, _, .seq _ _, h => nomatch h

/-- The merged diagram of a diagram of the fragment has a derivation from the diagram, in each
rule set that has the interchange rule and the copy rule. -/
def Diagram.mergeDerivation [DecEq S.Op] (inter : Rules.Map (Rules.interchange S) R)
    (copy : Rules.Map (Rules.copy S) R) {Γ : List Ty} {Qs : Exits Ty} (d : Diagram S Γ Qs)
    (h : d.Straight) : Diagram.Derivation R d (d.merge h) :=
  .trans (.symm (.agree d.renameId))
    (Diagram.mergeWithDerivation inter copy (fun D => D) (fun der => der) [] .nil
      (PortMap.id Γ) d h)

end Draft
