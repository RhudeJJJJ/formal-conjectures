/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode197
import Proofs.RadenkovicGutmanD43Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[245,0],[0,0]],[[0,0],[0,0]],[[3413,0],[0,0]],[[0,0],[0,0]],[[20848,0],[0,0]],[[0,0],[0,0]],[[69857,0],[0,0]],[[0,0],[0,0]],[[138252,2],[2,0]],[[0,0],[0,0]],[[163740,145],[145,0]],[[0,0],[0,0]],[[112220,990],[990,0]],[[0,0],[0,0]],[[39695,2370],[2370,0]],[[0,0],[0,0]],[[4755,2168],[2168,0]],[[0,0],[0,0]],[[-387,645],[645,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
