/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode044
import Proofs.RadenkovicGutmanD40Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0,0]],[[-360,360],[360,2]],[[0,0],[0]],[[102,978],[978]],[[0,0],[0]],[[6686,928],[928]],[[0,0],[0]],[[20894,364],[364]],[[0,0],[0]],[[31268,56],[56]],[[0,0],[0]],[[26952,2],[2]],[[0]],[[14032]],[[0]],[[4398]],[[0]],[[788]],[[0]],[[70]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
