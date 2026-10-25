/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode049
import Proofs.RadenkovicGutmanD6Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0,0]],[[-54,90],[90,2]],[[0,0],[0]],[[684,318],[318]],[[0,0],[0]],[[5856,372],[372]],[[0,0],[0]],[[17006,176],[176]],[[0,0],[0]],[[25564,34],[34]],[[0,0],[0]],[[22368,2],[2]],[[0]],[[11842]],[[0]],[[3782]],[[0]],[[694]],[[0]],[[64]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
