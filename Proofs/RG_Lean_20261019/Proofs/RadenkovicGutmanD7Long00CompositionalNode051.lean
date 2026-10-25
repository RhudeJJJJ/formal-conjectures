/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode049
import Proofs.RadenkovicGutmanD7Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,7]],[[0,0],[0,0]],[[-63,105],[105,2]],[[0,0],[0]],[[795,368],[368]],[[0,0],[0]],[[6779,426],[426]],[[0,0],[0]],[[19608,198],[198]],[[0,0],[0]],[[29348,37],[37]],[[0,0],[0]],[[25548,2],[2]],[[0]],[[13437]],[[0]],[[4252]],[[0]],[[769]],[[0]],[[69]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
