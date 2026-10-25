/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode197
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[155,0],[0,0]],[[0,0],[0,0]],[[2063,0],[0,0]],[[0,0],[0,0]],[[12388,0],[0,0]],[[0,0],[0,0]],[[41147,0],[0,0]],[[0,0],[0,0]],[[81012,2],[2,0]],[[0,0],[0,0]],[[95628,91],[91,0]],[[0,0],[0,0]],[[65384,594],[594,0]],[[0,0],[0,0]],[[23081,1398],[1398,0]],[[0,0],[0,0]],[[2757,1268],[1268,0]],[[0,0],[0,0]],[[-225,375],[375,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
