/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode049
import Proofs.RadenkovicGutmanD16Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,16]],[[0,0],[0,0]],[[-144,240],[240,2]],[[0,0],[0]],[[1794,818],[818]],[[0,0],[0]],[[15086,912],[912]],[[0,0],[0]],[[43026,396],[396]],[[0,0],[0]],[[63404,64],[64]],[[0,0],[0]],[[54168,2],[2]],[[0]],[[27792]],[[0]],[[8482]],[[0]],[[1444]],[[0]],[[114]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
