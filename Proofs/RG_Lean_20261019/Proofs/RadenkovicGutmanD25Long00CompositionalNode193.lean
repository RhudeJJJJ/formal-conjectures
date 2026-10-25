/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode192
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[55,0],[0,0]],[[0,0],[0,0]],[[563,0],[0,0]],[[0,0],[0,0]],[[2988,0],[0,0]],[[0,0],[0,0]],[[9247,0],[0,0]],[[0,0],[0,0]],[[17412,2],[2,0]],[[0,0],[0,0]],[[19928,41],[41,0]],[[0,0],[0,0]],[[13184,244],[244,0]],[[0,0],[0,0]],[[4181,598],[598,0]],[[0,0],[0,0]],[[57,618],[618,0]],[[0,0],[0,0]],[[-225,225],[225,2]],[[0],[0,0]],[[0],[0,25]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
