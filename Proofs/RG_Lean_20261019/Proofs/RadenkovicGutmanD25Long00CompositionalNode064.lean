/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode062
import Proofs.RadenkovicGutmanD25Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0,0]],[[225,375],[375,2]],[[0,0],[0]],[[6243,1268],[1268]],[[0,0],[0]],[[32743,1398],[1398]],[[0,0],[0]],[[76094,594],[594]],[[0,0],[0]],[[96760,91],[91]],[[0,0],[0]],[[73088,2],[2]],[[0]],[[33697]],[[0]],[[9362]],[[0]],[[1469]],[[0]],[[109]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
