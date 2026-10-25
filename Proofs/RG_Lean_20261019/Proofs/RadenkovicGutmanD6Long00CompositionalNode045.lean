/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode044
import Proofs.RadenkovicGutmanD6Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0,0]],[[-54,54],[54,2]],[[0,0],[0]],[[0,162],[162]],[[0,0],[0]],[[1008,180],[180]],[[0,0],[0]],[[3418,92],[92]],[[0,0],[0]],[[5564,22],[22]],[[0,0],[0]],[[5328,2],[2]],[[0]],[[3186]],[[0]],[[1202]],[[0]],[[278]],[[0]],[[36]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
