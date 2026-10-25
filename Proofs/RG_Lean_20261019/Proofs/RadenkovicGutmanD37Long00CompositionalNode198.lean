/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode197
import Proofs.RadenkovicGutmanD37Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[215,0],[0,0]],[[0,0],[0,0]],[[2963,0],[0,0]],[[0,0],[0,0]],[[18028,0],[0,0]],[[0,0],[0,0]],[[60287,0],[0,0]],[[0,0],[0,0]],[[119172,2],[2,0]],[[0,0],[0,0]],[[141036,127],[127,0]],[[0,0],[0,0]],[[96608,858],[858,0]],[[0,0],[0,0]],[[34157,2046],[2046,0]],[[0,0],[0,0]],[[4089,1868],[1868,0]],[[0,0],[0,0]],[[-333,555],[555,2]],[[0],[0,0]],[[0],[0,37]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
