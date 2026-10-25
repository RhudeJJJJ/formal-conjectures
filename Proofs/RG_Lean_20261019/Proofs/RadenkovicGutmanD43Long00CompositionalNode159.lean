/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode037
import Proofs.RadenkovicGutmanD43Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-41],[0]],[[0,0],[0]],[[-615,0],[0,0]],[[0,0],[0,0]],[[-3854,0],[0,0]],[[0,0],[0,0]],[[-13079,0],[0,0]],[[0,0],[0,0]],[[-26076,0],[0,0]],[[0,0],[0,0]],[[-30996,-41],[-41,0]],[[0,0],[0,0]],[[-21074,-328],[-328,0]],[[0,0],[0,0]],[[-6847,-902],[-902,0]],[[0,0],[0,0]],[[-123,-984],[-984,0]],[[0,0],[0,0]],[[369,-369],[-369,0]],[[0],[0,0]],[[0],[0,-41]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
