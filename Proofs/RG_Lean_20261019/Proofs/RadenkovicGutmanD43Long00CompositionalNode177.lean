/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode174
import Proofs.RadenkovicGutmanD43Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1394,0],[0,0]],[[0,0],[0,0]],[[-10004,0],[0,0]],[[0,0],[0,0]],[[-39442,0],[0,0]],[[0,0],[0,0]],[[-93152,0],[0,0]],[[0,0],[0,0]],[[-134808,-82],[-82,0]],[[0,0],[0,0]],[[-117260,-656],[-656,0]],[[0,0],[0,0]],[[-57154,-1804],[-1804,0]],[[0,0],[0,0]],[[-13038,-1968],[-1968,0]],[[0,0],[0,0]],[[-738,-738],[-738,0]],[[0],[0,0]],[[0],[0,-82]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
