/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode049
import Proofs.RadenkovicGutmanD45Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,45]],[[0,0],[0,0]],[[-405,675],[675,2]],[[0,0],[0]],[[5013,2268],[2268]],[[0,0],[0]],[[41853,2478],[2478]],[[0,0],[0]],[[118484,1034],[1034]],[[0,0],[0]],[[173140,151],[151]],[[0,0],[0]],[[146388,2],[2]],[[0]],[[74047]],[[0]],[[22112]],[[0]],[[3619]],[[0]],[[259]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
