/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode197
import Proofs.RadenkovicGutmanD44Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[250,0],[0,0]],[[0,0],[0,0]],[[3488,0],[0,0]],[[0,0],[0,0]],[[21318,0],[0,0]],[[0,0],[0,0]],[[71452,0],[0,0]],[[0,0],[0,0]],[[141432,2],[2,0]],[[0,0],[0,0]],[[167524,148],[148,0]],[[0,0],[0,0]],[[114822,1012],[1012,0]],[[0,0],[0,0]],[[40618,2424],[2424,0]],[[0,0],[0,0]],[[4866,2218],[2218,0]],[[0,0],[0,0]],[[-396,660],[660,2]],[[0],[0,0]],[[0],[0,44]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
