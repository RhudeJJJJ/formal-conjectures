/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode037
import Proofs.RadenkovicGutmanD25Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-23],[0]],[[0,0],[0]],[[-345,0],[0,0]],[[0,0],[0,0]],[[-2162,0],[0,0]],[[0,0],[0,0]],[[-7337,0],[0,0]],[[0,0],[0,0]],[[-14628,0],[0,0]],[[0,0],[0,0]],[[-17388,-23],[-23,0]],[[0,0],[0,0]],[[-11822,-184],[-184,0]],[[0,0],[0,0]],[[-3841,-506],[-506,0]],[[0,0],[0,0]],[[-69,-552],[-552,0]],[[0,0],[0,0]],[[207,-207],[-207,0]],[[0],[0,0]],[[0],[0,-23]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
