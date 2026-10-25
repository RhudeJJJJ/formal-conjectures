/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode198
import Proofs.RadenkovicGutmanD26Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[164,0],[0,0]],[[0,0],[0,0]],[[2194,0],[0,0]],[[0,0],[0,0]],[[13182,0],[0,0]],[[0,0],[0,0]],[[43742,0],[0,0]],[[0,0],[0,0]],[[85968,2],[2,0]],[[0,0],[0,0]],[[101244,94],[94,0]],[[0,0],[0,0]],[[69046,616],[616,0]],[[0,0],[0,0]],[[24316,1452],[1452,0]],[[0,0],[0,0]],[[2904,1318],[1318,0]],[[0,0],[0,0]],[[-234,390],[390,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
