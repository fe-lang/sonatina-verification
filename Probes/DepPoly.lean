import Draft.Checks.Diagram
import Draft.Checks.Countdown

/-! Probe: structures of the implementation that have the form of `DepPoly`. -/

set_option autoImplicit false
set_option genInjectivity false

open Prelude Container

namespace Draft

universe u v

variable {Ty : Type} {S : Signature Ty} {X : Ty → Type}

/-! 1. The relation of calls with a runtime. -/

/-- The interface with a runtime in each response. -/
def withRuntime (C : Container.{0, 0}) (R : Type u) : Container.{0, u} :=
  ⟨C.Shape, fun a => C.Pos a × R⟩

/-- A relation of calls is a specification of that interface: the precondition is the
runtime before the call, and the postcondition is on the response and the runtime after. -/
def Signature.Calls.spec {R : Type u} (T : Signature.Calls.{u, v} S X R) :
    DepPoly.{0, u, u, v} (withRuntime (S.interface X) R) where
  Pre _ := R
  Post a s p := T a s p.1 p.2

/-- A specification with the runtime as its precondition is a relation of calls. -/
def Signature.Calls.ofSpec {R : Type u}
    (Post : (a : (S.interface X).Shape) → R → (S.interface X).Pos a × R → Type v) :
    Signature.Calls.{u, v} S X R :=
  fun a s r s' => Post a s (r, s')

def Signature.Calls.ofSpecSpec {R : Type u} (T : Signature.Calls.{u, v} S X R) :
    Signature.Calls.ofSpec T.spec.Post ≡ T := .refl

def Signature.Calls.specOfSpec {R : Type u}
    (Post : (a : (S.interface X).Shape) → R → (S.interface X).Pos a × R → Type v) :
    (Signature.Calls.ofSpec (S := S) Post).spec.Post ≡ Post := .refl

/-- The run family of a diagram has the same form: a specification of the interface of the
diagram as one operation, with the runtime as its precondition. -/
def Diagram.runSpec {R : Type u} (T : Signature.Calls.{u, v} S X R) {Γ : List Ty}
    {Qs : Exits Ty} (d : Diagram S Γ Qs) :
    DepPoly.{0, u, u, max u v} (withRuntime ⟨All X Γ, fun _ => Qs.At X⟩ R) where
  Pre _ := R
  Post env s p := d.Runs T (env, s) p

/-! 2. An implementation that returns without a call. -/

/-- The specification that admits no call. -/
def noCall (D : Container.{0, 0}) : DepPoly.{0, 0, 0, 0} D where
  Pre _ := PEmpty
  Post _ e _ := nomatch e

variable {C D : Container.{0, 0}}

/-- Evidence against the specification that admits no call gives a returned value. -/
def returned {α : Type} {Q : α → Type} {x : Free D α} (h : FreeDep (noCall D) Q x) :
    (value : α) × (Free.Agreement x (.pure value) × Q value) :=
  FreeDep.casesOn
    (motive := fun x _ => (value : α) × (Free.Agreement x (.pure value) × Q value)) h
    (fun {value} q => ⟨value, .pure .refl, q⟩)
    (fun pre _ => nomatch pre)

def Impl.Returns.toDep {f : Impl C D} {a : C.Shape} (r : f.Returns a) :
    FreeDep (noCall D) (fun i => i ≡ r.response) (f a) :=
  FreeDep.reindex r.agrees.symm (.pure .refl)

def Impl.Returns.ofDep {f : Impl C D} {a : C.Shape} {Q : C.Pos a → Type}
    (h : FreeDep (noCall D) Q (f a)) : f.Returns a :=
  ⟨(returned h).1, (returned h).2.1⟩

/-- The pure operations are a precondition on the request interface. -/
def Signature.pureSpec (S : Signature Ty) (X : Ty → Type) : DepPoly.{0, 0, 0, 0} (S.interface X) where
  Pre a := S.kind a.1 ≡ .pure
  Post _ _ _ := PUnit

/-- "Each pure operation returns without a call" is a verified implementation. -/
def Signature.Returns.toDep {D : Container.{0, 0}} {impl : Impl (S.interface X) D}
    (h : S.Returns impl) : ImplDep (S.pureSpec X) (noCall D) impl :=
  fun a pre => FreeDep.reindex (h a.1 pre a.2).agrees.symm (.pure ⟨⟩)

def Signature.Returns.ofDep {D : Container.{0, 0}} {impl : Impl (S.interface X) D}
    (h : ImplDep (S.pureSpec X) (noCall D) impl) : S.Returns impl :=
  fun o pure args => Impl.Returns.ofDep (h ⟨o, args⟩ pure)

/-! 3. The frame. -/

variable {α : Type}

/-- The function meaning of a frame with a copairing uses the copairing at pairs only: a case
of the bypass, and then a case of the exit of the shared diagram. -/
def frameCurried {P M K : Boundary Ty} {Qs : Exits Ty} {Δ : List Ty}
    (stop : Free (S.interface X) α) (n : Nat)
    (kept : (c : P.Case) → M.At (Port c.1)) (args : (c : P.Case) → PortMap c.1 Δ)
    (shared : Diagram S Δ [K]) (each : (c : (M.product K).Case) → Diagram S c.1 Qs)
    (r : P.At X) (rest : Qs.At X → Free (S.interface X) α) :
    (Continuation.frame kept args shared (.copair each)).run stop n r rest ≡
      shared.run stop n (r.2.select (args r.1)) (Exits.At.only fun out =>
        ((fun (m : M.Case) (k : K.Case) => each (Boundary.pair m k)) (kept r.1).1 out.1).run
          stop n (out.2.append (r.2.select (kept r.1).2)) rest) :=
  .refl

end Draft

/-! The check of the countdown: the relation of calls is the graph of a state runner. -/

namespace Draft.Checks.Countdown

open Draft

/-- A state runner: a response and a runtime for each request and each runtime before. -/
def runner : (a : (withRuntime (sig.interface Value) Nat).Shape) → (calls.spec).Pre a →
    (withRuntime (sig.interface Value) Nat).Pos a :=
  handle

/-- The runner has the postcondition at its own response. -/
def runnerEvidence (a : (sig.interface Value).Shape) (s : Nat) :
    calls.spec.Post a s (runner a s) := .refl

end Draft.Checks.Countdown

#print axioms Draft.Signature.Returns.toDep
#print axioms Draft.Signature.Returns.ofDep
#print axioms Draft.frameCurried
#print axioms Draft.Signature.Calls.specOfSpec
