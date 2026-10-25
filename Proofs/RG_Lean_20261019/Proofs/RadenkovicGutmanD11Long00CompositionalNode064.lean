/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode062
import Proofs.RadenkovicGutmanD11Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,11]],[[0,0],[0,0]],[[99,165],[165,2]],[[0,0],[0]],[[2757,568],[568]],[[0,0],[0]],[[14585,642],[642]],[[0,0],[0]],[[34262,286],[286]],[[0,0],[0]],[[44176,49],[49]],[[0,0],[0]],[[34000,2],[2]],[[0]],[[16099]],[[0]],[[4658]],[[0]],[[783]],[[0]],[[67]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
