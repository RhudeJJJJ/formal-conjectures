/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode197
import Proofs.RadenkovicGutmanD30Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[180,0],[0,0]],[[0,0],[0,0]],[[2438,0],[0,0]],[[0,0],[0,0]],[[14738,0],[0,0]],[[0,0],[0,0]],[[49122,0],[0,0]],[[0,0],[0,0]],[[96912,2],[2,0]],[[0,0],[0,0]],[[114548,106],[106,0]],[[0,0],[0,0]],[[78394,704],[704,0]],[[0,0],[0,0]],[[27696,1668],[1668,0]],[[0,0],[0,0]],[[3312,1518],[1518,0]],[[0,0],[0,0]],[[-270,450],[450,2]],[[0],[0,0]],[[0],[0,30]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
