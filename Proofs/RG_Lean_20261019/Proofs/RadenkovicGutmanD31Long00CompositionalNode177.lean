/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode174
import Proofs.RadenkovicGutmanD31Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-58],[0]],[[0,0],[0]],[[-986,0],[0,0]],[[0,0],[0,0]],[[-7076,0],[0,0]],[[0,0],[0,0]],[[-27898,0],[0,0]],[[0,0],[0,0]],[[-65888,0],[0,0]],[[0,0],[0,0]],[[-95352,-58],[-58,0]],[[0,0],[0,0]],[[-82940,-464],[-464,0]],[[0,0],[0,0]],[[-40426,-1276],[-1276,0]],[[0,0],[0,0]],[[-9222,-1392],[-1392,0]],[[0,0],[0,0]],[[-522,-522],[-522,0]],[[0],[0,0]],[[0],[0,-58]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
