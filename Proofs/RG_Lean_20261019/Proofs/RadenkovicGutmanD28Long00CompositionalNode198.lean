/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode197
import Proofs.RadenkovicGutmanD28Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[170,0],[0,0]],[[0,0],[0,0]],[[2288,0],[0,0]],[[0,0],[0,0]],[[13798,0],[0,0]],[[0,0],[0,0]],[[45932,0],[0,0]],[[0,0],[0,0]],[[90552,2],[2,0]],[[0,0],[0,0]],[[106980,100],[100,0]],[[0,0],[0,0]],[[73190,660],[660,0]],[[0,0],[0,0]],[[25850,1560],[1560,0]],[[0,0],[0,0]],[[3090,1418],[1418,0]],[[0,0],[0,0]],[[-252,420],[420,2]],[[0],[0,0]],[[0],[0,28]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
