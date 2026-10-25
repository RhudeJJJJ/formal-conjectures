/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode174
import Proofs.RadenkovicGutmanD7Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-170,0],[0,0]],[[0,0],[0,0]],[[-1220,0],[0,0]],[[0,0],[0,0]],[[-4810,0],[0,0]],[[0,0],[0,0]],[[-11360,0],[0,0]],[[0,0],[0,0]],[[-16440,-10],[-10,0]],[[0,0],[0,0]],[[-14300,-80],[-80,0]],[[0,0],[0,0]],[[-6970,-220],[-220,0]],[[0,0],[0,0]],[[-1590,-240],[-240,0]],[[0,0],[0,0]],[[-90,-90],[-90,0]],[[0],[0,0]],[[0],[0,-10]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
