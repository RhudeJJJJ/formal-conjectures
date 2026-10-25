/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode049
import Proofs.RadenkovicGutmanD39Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0,0]],[[-351,585],[585,2]],[[0,0],[0]],[[4347,1968],[1968]],[[0,0],[0]],[[36315,2154],[2154]],[[0,0],[0]],[[102872,902],[902]],[[0,0],[0]],[[150436,133],[133]],[[0,0],[0]],[[127308,2],[2]],[[0]],[[64477]],[[0]],[[19292]],[[0]],[[3169]],[[0]],[[229]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
