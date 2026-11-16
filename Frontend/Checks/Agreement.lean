import Stele.Interp
import Frontend.Checks.Stele

/-! The run of a compiled function, and the run of the same function by the interpreter of
Stele.

Each check runs one transition of the contract two times, from one value of the call, one list
of arguments, and one storage. The first run is the run of the diagram of the translated
function. The second run is the run of the body by the executable semantics of EquiVM, with the
Solidity layout of the storage of the contract. The two observations are equal: the returned
integer and the values of the storage variables, or a stop at a `revert`.

These checks are compiled observations. -/

set_option autoImplicit false

namespace Frontend.Checks

/-- The configuration of the interpreter: the Solidity layout of the storage of the
contract. -/
def config : Stele.Config :=
  { storageBackend := solidityStorage! [demo.structs] [demo.storage]
    externalABI := Stele.defaultExternalCallABI
    selfDeployment := fun code _ => some code }

/-- The account of the contract. -/
def owner : EVM.Address := .ofNat 256

/-- The storage of the account, with the listed values at its first slots. -/
def storageOf (slots : List Int) : Ethereum.Storage :=
  ((List.range slots.length).zip slots).foldl
    (fun m (k, v) => m.insert (.ofNat k) (.ofNat v.toNat)) ∅

/-- The state of the machine: the value of the call, and the storage of the account. -/
def machine (callvalue : Int) (slots : List Int) : EVM.State :=
  { (default : EVM.State) with
    executionEnv :=
      { (default : Ethereum.ExecutionEnv) with
        codeOwner := owner, perm := true, weiValue := .ofNat callvalue.toNat }
    accountMap := (∅ : Ethereum.AccountMap).insert owner
      { (default : Ethereum.Account) with storage := storageOf slots } }

/-- An oracle for a body that makes no call. -/
def oracle : Stele.Interp.Oracle Unit :=
  { call := fun _ _ _ => .error "no call"
    create := fun _ _ _ => .error "no create"
    gasLeft := fun ω _ => (.ofNat 0, ω) }

/-- The locals of a frame, from the parameters and their values. -/
def localsOf : List Stele.Param → List Int → Stele.Store
  | p :: ps, v :: vs => (localsOf ps vs).insert p.name (.int v)
  | _, _ => ∅

/-- The value of a storage variable after a run. -/
def slotValue (frame : Stele.Frame) (state : EVM.State) (d : Stele.StorageDecl) : Int :=
  match Stele.evalExpr? config frame state (.storage { base := d.name }) with
  | .ok (.int v) => v
  | _ => -1

/-- The observation of the run of a transition by the interpreter of Stele. -/
def interpret (name : String) (fuel : Nat) (callvalue : Int) (params : List Int)
    (slots : List Int) : Observation :=
  match demo.transitions.find? (·.name == name) with
  | none => .rejected (.noTransition name)
  | some t =>
      let frame : Stele.Frame := { contract := demo, locals := localsOf t.params params }
      match (Stele.Interp.execFuncBody fuel oracle () config frame (machine callvalue slots)
          t.body).1 with
      | .result (.returned frame' state' (some [.int v])) =>
          .returned v ((demo.storage.take slots.length).map (slotValue frame' state'))
      | .result .reverted => .reverted
      | .outOfFuel => .limit
      | _ => .rejected .statement

/-- The two observations of one transition are equal. -/
def agree (name : String) (callvalue : Int) (params : List Int) (slots : List Int) : Bool :=
  observe name 64 (.int callvalue :: params.map .int) slots
    == interpret name 4096 callvalue params slots

#guard agree "update" 0 [3, 4] [10, 0]
#guard agree "update" 1 [3, 4] [10, 0]
#guard agree "update" 0 [1, 2 ^ 256 - 1] [0, 0]
#guard agree "update" 0 [2 ^ 200, 2 ^ 100] [2 ^ 255, 7]
#guard agree "larger" 0 [3, 5] []
#guard agree "larger" 0 [7, 2] []
#guard agree "sum" 0 [4] []
#guard agree "sum" 0 [0] []
#guard agree "sum" 0 [20] []
#guard agree "guarded" 0 [7, 2] []
#guard agree "guarded" 0 [7, 0] []
#guard agree "lazy" 0 [7, 0] []
#guard agree "lazy" 0 [1, 2] []
#guard agree "lazy" 0 [7, 2] []
#guard agree "narrow" 0 [300] [0, 0]
#guard agree "narrow" 0 [255] [5, 9]

-- The interpreter gives the values that the compiled observations have.
#guard interpret "update" 4096 0 [3, 4] [10, 0] == .returned 22 [25, 0]
#guard interpret "narrow" 4096 0 [300] [0, 0] == .returned 44 [0, 44]
#guard interpret "guarded" 4096 0 [7, 0] [] == .reverted

end Frontend.Checks
