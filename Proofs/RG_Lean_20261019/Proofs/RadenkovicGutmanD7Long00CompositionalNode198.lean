/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode197
import Proofs.RadenkovicGutmanD7Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e198 : NestedArithmetic.Expr 3 := .times e197 e122
noncomputable def p198 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[65,0],[0,0]],[[0,0],[0,0]],[[713,0],[0,0]],[[0,0],[0,0]],[[3928,0],[0,0]],[[0,0],[0,0]],[[12437,0],[0,0]],[[0,0],[0,0]],[[23772,2],[2,0]],[[0,0],[0,0]],[[27516,37],[37,0]],[[0,0],[0,0]],[[18548,198],[198,0]],[[0,0],[0,0]],[[6467,426],[426,0]],[[0,0],[0,0]],[[759,368],[368,0]],[[0,0],[0,0]],[[-63,105],[105,2]],[[0],[0,0]],[[0],[0,7]]]
theorem step198 : p198=NestedArithmetic.mul p197 p122 := by decide +kernel
#print axioms step198
theorem h198 : NestedArithmetic.compile e198=p198 := StagedExprCompile.compile_times e198 e197 e122 p197 p122 p198 rfl h197 h122 step198
#print axioms h198
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
