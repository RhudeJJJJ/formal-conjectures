/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode197
import Proofs.RadenkovicGutmanD10Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[80,0],[0,0]],[[0,0],[0,0]],[[938,0],[0,0]],[[0,0],[0,0]],[[5338,0],[0,0]],[[0,0],[0,0]],[[17222,0],[0,0]],[[0,0],[0,0]],[[33312,2],[2,0]],[[0,0],[0,0]],[[38868,46],[46,0]],[[0,0],[0,0]],[[26354,264],[264,0]],[[0,0],[0,0]],[[9236,588],[588,0]],[[0,0],[0,0]],[[1092,518],[518,0]],[[0,0],[0,0]],[[-90,150],[150,2]],[[0],[0,0]],[[0],[0,10]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
