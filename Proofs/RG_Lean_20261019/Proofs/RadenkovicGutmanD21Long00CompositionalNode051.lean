/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode049
import Proofs.RadenkovicGutmanD21Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0,0]],[[-189,315],[315,2]],[[0,0],[0]],[[2349,1068],[1068]],[[0,0],[0]],[[19701,1182],[1182]],[[0,0],[0]],[[56036,506],[506]],[[0,0],[0]],[[82324,79],[79]],[[0,0],[0]],[[70068,2],[2]],[[0]],[[35767]],[[0]],[[10832]],[[0]],[[1819]],[[0]],[[139]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
