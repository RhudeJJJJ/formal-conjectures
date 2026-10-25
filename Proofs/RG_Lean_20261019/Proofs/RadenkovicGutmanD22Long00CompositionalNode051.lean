/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode049
import Proofs.RadenkovicGutmanD22Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,22]],[[0,0],[0,0]],[[-198,330],[330,2]],[[0,0],[0]],[[2460,1118],[1118]],[[0,0],[0]],[[20624,1236],[1236]],[[0,0],[0]],[[58638,528],[528]],[[0,0],[0]],[[86108,82],[82]],[[0,0],[0]],[[73248,2],[2]],[[0]],[[37362]],[[0]],[[11302]],[[0]],[[1894]],[[0]],[[144]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
