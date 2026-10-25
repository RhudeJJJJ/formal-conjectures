/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode197
import Proofs.RadenkovicGutmanD33Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[195,0],[0,0]],[[0,0],[0,0]],[[2663,0],[0,0]],[[0,0],[0,0]],[[16148,0],[0,0]],[[0,0],[0,0]],[[53907,0],[0,0]],[[0,0],[0,0]],[[106452,2],[2,0]],[[0,0],[0,0]],[[125900,115],[115,0]],[[0,0],[0,0]],[[86200,770],[770,0]],[[0,0],[0,0]],[[30465,1830],[1830,0]],[[0,0],[0,0]],[[3645,1668],[1668,0]],[[0,0],[0,0]],[[-297,495],[495,2]],[[0],[0,0]],[[0],[0,33]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
