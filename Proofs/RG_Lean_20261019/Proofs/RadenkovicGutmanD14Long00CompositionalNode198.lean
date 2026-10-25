/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode197
import Proofs.RadenkovicGutmanD14Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[100,0],[0,0]],[[0,0],[0,0]],[[1238,0],[0,0]],[[0,0],[0,0]],[[7218,0],[0,0]],[[0,0],[0,0]],[[23602,0],[0,0]],[[0,0],[0,0]],[[46032,2],[2,0]],[[0,0],[0,0]],[[54004,58],[58,0]],[[0,0],[0,0]],[[36762,352],[352,0]],[[0,0],[0,0]],[[12928,804],[804,0]],[[0,0],[0,0]],[[1536,718],[718,0]],[[0,0],[0,0]],[[-126,210],[210,2]],[[0],[0,0]],[[0],[0,14]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
