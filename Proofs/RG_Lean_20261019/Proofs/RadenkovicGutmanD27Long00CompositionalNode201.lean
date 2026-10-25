/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode198
import Proofs.RadenkovicGutmanD27Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[169,0],[0,0]],[[0,0],[0,0]],[[2269,0],[0,0]],[[0,0],[0,0]],[[13652,0],[0,0]],[[0,0],[0,0]],[[45337,0],[0,0]],[[0,0],[0,0]],[[89148,2],[2,0]],[[0,0],[0,0]],[[105028,97],[97,0]],[[0,0],[0,0]],[[71648,638],[638,0]],[[0,0],[0,0]],[[25239,1506],[1506,0]],[[0,0],[0,0]],[[3015,1368],[1368,0]],[[0,0],[0,0]],[[-243,405],[405,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
