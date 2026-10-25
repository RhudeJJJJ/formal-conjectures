/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode197
import Proofs.RadenkovicGutmanD45Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[255,0],[0,0]],[[0,0],[0,0]],[[3563,0],[0,0]],[[0,0],[0,0]],[[21788,0],[0,0]],[[0,0],[0,0]],[[73047,0],[0,0]],[[0,0],[0,0]],[[144612,2],[2,0]],[[0,0],[0,0]],[[171308,151],[151,0]],[[0,0],[0,0]],[[117424,1034],[1034,0]],[[0,0],[0,0]],[[41541,2478],[2478,0]],[[0,0],[0,0]],[[4977,2268],[2268,0]],[[0,0],[0,0]],[[-405,675],[675,2]],[[0],[0,0]],[[0],[0,45]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
