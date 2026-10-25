/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode062
import Proofs.RadenkovicGutmanD13Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,13]],[[0,0],[0,0]],[[117,195],[195,2]],[[0,0],[0]],[[3255,668],[668]],[[0,0],[0]],[[17179,750],[750]],[[0,0],[0]],[[40238,330],[330]],[[0,0],[0]],[[51688,55],[55]],[[0,0],[0]],[[39584,2],[2]],[[0]],[[18613]],[[0]],[[5330]],[[0]],[[881]],[[0]],[[73]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
