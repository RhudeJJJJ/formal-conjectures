/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode197
import Proofs.RadenkovicGutmanD9Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[75,0],[0,0]],[[0,0],[0,0]],[[863,0],[0,0]],[[0,0],[0,0]],[[4868,0],[0,0]],[[0,0],[0,0]],[[15627,0],[0,0]],[[0,0],[0,0]],[[30132,2],[2,0]],[[0,0],[0,0]],[[35084,43],[43,0]],[[0,0],[0,0]],[[23752,242],[242,0]],[[0,0],[0,0]],[[8313,534],[534,0]],[[0,0],[0,0]],[[981,468],[468,0]],[[0,0],[0,0]],[[-81,135],[135,2]],[[0],[0,0]],[[0],[0,9]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
