/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode049
import Proofs.RadenkovicGutmanD34Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,34]],[[0,0],[0,0]],[[-306,510],[510,2]],[[0,0],[0]],[[3792,1718],[1718]],[[0,0],[0]],[[31700,1884],[1884]],[[0,0],[0]],[[89862,792],[792]],[[0,0],[0]],[[131516,118],[118]],[[0,0],[0]],[[111408,2],[2]],[[0]],[[56502]],[[0]],[[16942]],[[0]],[[2794]],[[0]],[[204]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
