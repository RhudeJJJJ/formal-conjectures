/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode177
import Proofs.RadenkovicGutmanD7Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-170,0],[0,0]],[[0,0],[0,0]],[[-1220,0],[0,0]],[[0,0],[0,0]],[[-4810,0],[0,0]],[[0,0],[0,0]],[[-11360,0],[0,0]],[[0,0],[0,0]],[[-16440,-10],[-10,0]],[[0,0],[0,0]],[[-14300,-80],[-80,0]],[[0,0],[0,0]],[[-6970,-220],[-220,0]],[[0,0],[0,0]],[[-1590,-240],[-240,0]],[[0,0],[0,0]],[[-90,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
