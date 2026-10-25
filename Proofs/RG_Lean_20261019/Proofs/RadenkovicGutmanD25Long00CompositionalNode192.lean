/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode191
import Proofs.RadenkovicGutmanD25Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[563,0],[0,0]],[[0,0],[0,0]],[[2988,0],[0,0]],[[0,0],[0,0]],[[9247,0],[0,0]],[[0,0],[0,0]],[[17412,2],[2,0]],[[0,0],[0,0]],[[19928,41],[41,0]],[[0,0],[0,0]],[[13184,244],[244,0]],[[0,0],[0,0]],[[4181,598],[598,0]],[[0,0],[0,0]],[[57,618],[618,0]],[[0,0],[0,0]],[[-225,225],[225,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
