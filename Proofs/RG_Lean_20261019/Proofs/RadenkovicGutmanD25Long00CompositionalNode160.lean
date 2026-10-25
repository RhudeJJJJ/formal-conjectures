/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode159
import Proofs.RadenkovicGutmanD25Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-23],[0]],[[0,0],[0]],[[-345,0],[0,0]],[[0,0],[0,0]],[[-2162,0],[0,0]],[[0,0],[0,0]],[[-7337,0],[0,0]],[[0,0],[0,0]],[[-14628,0],[0,0]],[[0,0],[0,0]],[[-17388,-23],[-23,0]],[[0,0],[0,0]],[[-11822,-184],[-184,0]],[[0,0],[0,0]],[[-3841,-506],[-506,0]],[[0,0],[0,0]],[[-69,-552],[-552,0]],[[0,0],[0,0]],[[207,-207],[-207,0]],[[0],[0,0]],[[0],[0,-23]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
