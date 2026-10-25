/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode197
import Proofs.RadenkovicGutmanD34Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[200,0],[0,0]],[[0,0],[0,0]],[[2738,0],[0,0]],[[0,0],[0,0]],[[16618,0],[0,0]],[[0,0],[0,0]],[[55502,0],[0,0]],[[0,0],[0,0]],[[109632,2],[2,0]],[[0,0],[0,0]],[[129684,118],[118,0]],[[0,0],[0,0]],[[88802,792],[792,0]],[[0,0],[0,0]],[[31388,1884],[1884,0]],[[0,0],[0,0]],[[3756,1718],[1718,0]],[[0,0],[0,0]],[[-306,510],[510,2]],[[0],[0,0]],[[0],[0,34]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
