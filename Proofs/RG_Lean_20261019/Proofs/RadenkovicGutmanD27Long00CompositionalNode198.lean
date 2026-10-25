/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode197
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[165,0],[0,0]],[[0,0],[0,0]],[[2213,0],[0,0]],[[0,0],[0,0]],[[13328,0],[0,0]],[[0,0],[0,0]],[[44337,0],[0,0]],[[0,0],[0,0]],[[87372,2],[2,0]],[[0,0],[0,0]],[[103196,97],[97,0]],[[0,0],[0,0]],[[70588,638],[638,0]],[[0,0],[0,0]],[[24927,1506],[1506,0]],[[0,0],[0,0]],[[2979,1368],[1368,0]],[[0,0],[0,0]],[[-243,405],[405,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
