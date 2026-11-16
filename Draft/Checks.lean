import Draft.Checks.Polynomial
import Draft.Checks.Dependent
import Draft.Checks.Free
import Draft.Checks.Verified
import Draft.Checks.Order
import Draft.Checks.Composite
import Draft.Checks.Fold
import Draft.Checks.Diagram
import Draft.Checks.Countdown
import Draft.Checks.Lift

/-! Named kernel checks.

Each check has `smartUnfolding false`, for its module or for the check. The elaborator then
unfolds a structural recursion by its recursor, as the kernel does. With smart unfolding, the
elaborator reduces the recursion argument of a call again at each level, and the cost of a
nested run grows by a constant factor for each level. A module that defines diagrams has the
option for each check only: with the option, the elaborator writes a computed implicit argument
in recursor form, and the code generator rejects the definition. -/
