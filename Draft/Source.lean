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
thus has one run. -/

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

end Draft
