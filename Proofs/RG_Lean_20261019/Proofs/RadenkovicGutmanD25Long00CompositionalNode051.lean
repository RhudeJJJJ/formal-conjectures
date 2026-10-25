/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode049
import Proofs.RadenkovicGutmanD25Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0,0]],[[-225,375],[375,2]],[[0,0],[0]],[[2793,1268],[1268]],[[0,0],[0]],[[23393,1398],[1398]],[[0,0],[0]],[[66444,594],[594]],[[0,0],[0]],[[97460,91],[91]],[[0,0],[0]],[[82788,2],[2]],[[0]],[[42147]],[[0]],[[12712]],[[0]],[[2119]],[[0]],[[159]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
