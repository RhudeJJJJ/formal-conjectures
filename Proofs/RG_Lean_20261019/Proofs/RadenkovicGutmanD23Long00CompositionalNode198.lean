/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode197
import Proofs.RadenkovicGutmanD23Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[145,0],[0,0]],[[0,0],[0,0]],[[1913,0],[0,0]],[[0,0],[0,0]],[[11448,0],[0,0]],[[0,0],[0,0]],[[37957,0],[0,0]],[[0,0],[0,0]],[[74652,2],[2,0]],[[0,0],[0,0]],[[88060,85],[85,0]],[[0,0],[0,0]],[[60180,550],[550,0]],[[0,0],[0,0]],[[21235,1290],[1290,0]],[[0,0],[0,0]],[[2535,1168],[1168,0]],[[0,0],[0,0]],[[-207,345],[345,2]],[[0],[0,0]],[[0],[0,23]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
