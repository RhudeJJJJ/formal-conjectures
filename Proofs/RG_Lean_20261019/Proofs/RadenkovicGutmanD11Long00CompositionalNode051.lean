/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode049
import Proofs.RadenkovicGutmanD11Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0,0]],[[-99,165],[165,2]],[[0,0],[0]],[[1239,568],[568]],[[0,0],[0]],[[10471,642],[642]],[[0,0],[0]],[[30016,286],[286]],[[0,0],[0]],[[44484,49],[49]],[[0,0],[0]],[[38268,2],[2]],[[0]],[[19817]],[[0]],[[6132]],[[0]],[[1069]],[[0]],[[89]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
