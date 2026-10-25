/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode062
import Proofs.RadenkovicGutmanD24Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0,0]],[[216,360],[360,2]],[[0,0],[0]],[[5994,1218],[1218]],[[0,0],[0]],[[31446,1344],[1344]],[[0,0],[0]],[[73106,572],[572]],[[0,0],[0]],[[93004,88],[88]],[[0,0],[0]],[[70296,2],[2]],[[0]],[[32440]],[[0]],[[9026]],[[0]],[[1420]],[[0]],[[106]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
