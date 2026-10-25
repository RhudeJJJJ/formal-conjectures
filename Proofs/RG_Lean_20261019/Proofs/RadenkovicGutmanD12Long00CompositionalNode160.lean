/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode159
import Proofs.RadenkovicGutmanD12Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e160 : NestedArithmetic.Expr 3 := .times e159 e122
noncomputable def p160 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-150,0],[0,0]],[[0,0],[0,0]],[[-940,0],[0,0]],[[0,0],[0,0]],[[-3190,0],[0,0]],[[0,0],[0,0]],[[-6360,0],[0,0]],[[0,0],[0,0]],[[-7560,-10],[-10,0]],[[0,0],[0,0]],[[-5140,-80],[-80,0]],[[0,0],[0,0]],[[-1670,-220],[-220,0]],[[0,0],[0,0]],[[-30,-240],[-240,0]],[[0,0],[0,0]],[[90,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step160 : p160=NestedArithmetic.mul p159 p122 := by decide +kernel
#print axioms step160
theorem h160 : NestedArithmetic.compile e160=p160 := StagedExprCompile.compile_times e160 e159 e122 p159 p122 p160 rfl h159 h122 step160
#print axioms h160
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
