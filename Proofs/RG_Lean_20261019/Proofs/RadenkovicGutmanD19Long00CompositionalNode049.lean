/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode045
import Proofs.RadenkovicGutmanD19Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,19]],[[0,0],[0,0]],[[-171,285],[285,2]],[[0,0],[0]],[[2091,968],[968]],[[0,0],[0]],[[17543,1074],[1074]],[[0,0],[0]],[[49772,462],[462]],[[0,0],[0]],[[72924,73],[73]],[[0,0],[0]],[[61932,2],[2]],[[0]],[[31577]],[[0]],[[9568]],[[0]],[[1613]],[[0]],[[125]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
