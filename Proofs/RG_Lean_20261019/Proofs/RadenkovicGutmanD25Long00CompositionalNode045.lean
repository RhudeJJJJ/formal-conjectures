/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode044
import Proofs.RadenkovicGutmanD25Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,25]],[[0,0],[0,0]],[[-225,225],[225,2]],[[0,0],[0]],[[57,618],[618]],[[0,0],[0]],[[4181,598],[598]],[[0,0],[0]],[[13184,244],[244]],[[0,0],[0]],[[19928,41],[41]],[[0,0],[0]],[[17412,2],[2]],[[0]],[[9247]],[[0]],[[2988]],[[0]],[[563]],[[0]],[[55]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
