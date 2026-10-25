/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode198
import Proofs.RadenkovicGutmanD20Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[134,0],[0,0]],[[0,0],[0,0]],[[1744,0],[0,0]],[[0,0],[0,0]],[[10362,0],[0,0]],[[0,0],[0,0]],[[34172,0],[0,0]],[[0,0],[0,0]],[[66888,2],[2,0]],[[0,0],[0,0]],[[78540,76],[76,0]],[[0,0],[0,0]],[[53434,484],[484,0]],[[0,0],[0,0]],[[18778,1128],[1128,0]],[[0,0],[0,0]],[[2238,1018],[1018,0]],[[0,0],[0,0]],[[-180,300],[300,2]],[[0],[0,0]],[[0],[0,20]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
