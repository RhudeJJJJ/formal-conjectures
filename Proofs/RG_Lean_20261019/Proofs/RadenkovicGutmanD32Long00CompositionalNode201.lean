/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode198
import Proofs.RadenkovicGutmanD32Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[194,0],[0,0]],[[0,0],[0,0]],[[2644,0],[0,0]],[[0,0],[0,0]],[[16002,0],[0,0]],[[0,0],[0,0]],[[53312,0],[0,0]],[[0,0],[0,0]],[[105048,2],[2,0]],[[0,0],[0,0]],[[123948,112],[112,0]],[[0,0],[0,0]],[[84658,748],[748,0]],[[0,0],[0,0]],[[29854,1776],[1776,0]],[[0,0],[0,0]],[[3570,1618],[1618,0]],[[0,0],[0,0]],[[-288,480],[480,2]],[[0],[0,0]],[[0],[0,32]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
