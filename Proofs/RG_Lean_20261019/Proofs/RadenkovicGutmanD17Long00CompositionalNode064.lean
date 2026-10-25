/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode062
import Proofs.RadenkovicGutmanD17Long00CompositionalNode063
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e064 : NestedArithmetic.Expr 3 := .plus e062 e063
noncomputable def p064 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0,0]],[[153,255],[255,2]],[[0,0],[0]],[[4251,868],[868]],[[0,0],[0]],[[22367,966],[966]],[[0,0],[0]],[[52190,418],[418]],[[0,0],[0]],[[66712,67],[67]],[[0,0],[0]],[[50752,2],[2]],[[0]],[[23641]],[[0]],[[6674]],[[0]],[[1077]],[[0]],[[85]],[[0]],[[2]]]
theorem step064 : p064=NestedHorner.add p062 p063 := by decide +kernel
#print axioms step064
theorem h064 : NestedArithmetic.compile e064=p064 := StagedExprCompile.compile_plus e064 e062 e063 p062 p063 p064 rfl h062 h063 step064
#print axioms h064
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
