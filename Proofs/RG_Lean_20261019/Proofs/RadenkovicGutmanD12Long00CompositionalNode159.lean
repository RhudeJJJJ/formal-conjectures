/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode037
import Proofs.RadenkovicGutmanD12Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e159 : NestedArithmetic.Expr 3 := .times e037 e158
noncomputable def p159 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-150,0],[0,0]],[[0,0],[0,0]],[[-940,0],[0,0]],[[0,0],[0,0]],[[-3190,0],[0,0]],[[0,0],[0,0]],[[-6360,0],[0,0]],[[0,0],[0,0]],[[-7560,-10],[-10,0]],[[0,0],[0,0]],[[-5140,-80],[-80,0]],[[0,0],[0,0]],[[-1670,-220],[-220,0]],[[0,0],[0,0]],[[-30,-240],[-240,0]],[[0,0],[0,0]],[[90,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step159 : p159=NestedArithmetic.mul p037 p158 := by decide +kernel
#print axioms step159
theorem h159 : NestedArithmetic.compile e159=p159 := StagedExprCompile.compile_times e159 e037 e158 p037 p158 p159 rfl h037 h158 step159
#print axioms h159
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
