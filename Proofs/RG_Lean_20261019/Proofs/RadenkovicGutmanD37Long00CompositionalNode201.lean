/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode198
import Proofs.RadenkovicGutmanD37Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[219,0],[0,0]],[[0,0],[0,0]],[[3019,0],[0,0]],[[0,0],[0,0]],[[18352,0],[0,0]],[[0,0],[0,0]],[[61287,0],[0,0]],[[0,0],[0,0]],[[120948,2],[2,0]],[[0,0],[0,0]],[[142868,127],[127,0]],[[0,0],[0,0]],[[97668,858],[858,0]],[[0,0],[0,0]],[[34469,2046],[2046,0]],[[0,0],[0,0]],[[4125,1868],[1868,0]],[[0,0],[0,0]],[[-333,555],[555,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
