/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanNestedArithmetic

/-!
# Exact equality for polynomial program syntax

Constructor equality checks rational and finite-index fields propositionally.
This instance is used only by subsequent explicit kernel expression equalities.
-/
namespace Gebendorfer.RadenkovicGutman.NestedArithmetic
deriving instance DecidableEq for Expr

def expressionDecidableEq (n : ℕ) : DecidableEq (Expr n) := inferInstance
#print axioms expressionDecidableEq
end Gebendorfer.RadenkovicGutman.NestedArithmetic
