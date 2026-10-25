/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode198
import Proofs.RadenkovicGutmanD24Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[154,0],[0,0]],[[0,0],[0,0]],[[2044,0],[0,0]],[[0,0],[0,0]],[[12242,0],[0,0]],[[0,0],[0,0]],[[40552,0],[0,0]],[[0,0],[0,0]],[[79608,2],[2,0]],[[0,0],[0,0]],[[93676,88],[88,0]],[[0,0],[0,0]],[[63842,572],[572,0]],[[0,0],[0,0]],[[22470,1344],[1344,0]],[[0,0],[0,0]],[[2682,1218],[1218,0]],[[0,0],[0,0]],[[-216,360],[360,2]],[[0],[0,0]],[[0],[0,24]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
