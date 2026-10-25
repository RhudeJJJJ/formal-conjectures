/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode193
import Proofs.RadenkovicGutmanD44Long00CompositionalNode196
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e197 : NestedArithmetic.Expr 3 := .plus e193 e196
noncomputable def p197 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[250,0],[0,0]],[[0,0],[0,0]],[[3488,0],[0,0]],[[0,0],[0,0]],[[21318,0],[0,0]],[[0,0],[0,0]],[[71452,0],[0,0]],[[0,0],[0,0]],[[141432,2],[2,0]],[[0,0],[0,0]],[[167524,148],[148,0]],[[0,0],[0,0]],[[114822,1012],[1012,0]],[[0,0],[0,0]],[[40618,2424],[2424,0]],[[0,0],[0,0]],[[4866,2218],[2218,0]],[[0,0],[0,0]],[[-396,660],[660,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step197 : p197=NestedHorner.add p193 p196 := by decide +kernel
#print axioms step197
theorem h197 : NestedArithmetic.compile e197=p197 := StagedExprCompile.compile_plus e197 e193 e196 p193 p196 p197 rfl h193 h196 step197
#print axioms h197
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
