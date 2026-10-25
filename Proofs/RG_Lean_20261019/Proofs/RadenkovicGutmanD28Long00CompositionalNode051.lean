/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode049
import Proofs.RadenkovicGutmanD28Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0,0]],[[-252,420],[420,2]],[[0,0],[0]],[[3126,1418],[1418]],[[0,0],[0]],[[26162,1560],[1560]],[[0,0],[0]],[[74250,660],[660]],[[0,0],[0]],[[108812,100],[100]],[[0,0],[0]],[[92328,2],[2]],[[0]],[[46932]],[[0]],[[14122]],[[0]],[[2344]],[[0]],[[174]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
