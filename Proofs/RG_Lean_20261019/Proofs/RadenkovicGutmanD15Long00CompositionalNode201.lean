/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode198
import Proofs.RadenkovicGutmanD15Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[109,0],[0,0]],[[0,0],[0,0]],[[1369,0],[0,0]],[[0,0],[0,0]],[[8012,0],[0,0]],[[0,0],[0,0]],[[26197,0],[0,0]],[[0,0],[0,0]],[[50988,2],[2,0]],[[0,0],[0,0]],[[59620,61],[61,0]],[[0,0],[0,0]],[[40424,374],[374,0]],[[0,0],[0,0]],[[14163,858],[858,0]],[[0,0],[0,0]],[[1683,768],[768,0]],[[0,0],[0,0]],[[-135,225],[225,2]],[[0],[0,0]],[[0],[0,15]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
