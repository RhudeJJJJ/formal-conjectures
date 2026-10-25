/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode177
import Proofs.RadenkovicGutmanD43Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1394,0],[0,0]],[[0,0],[0,0]],[[-10004,0],[0,0]],[[0,0],[0,0]],[[-39442,0],[0,0]],[[0,0],[0,0]],[[-93152,0],[0,0]],[[0,0],[0,0]],[[-134808,-82],[-82,0]],[[0,0],[0,0]],[[-117260,-656],[-656,0]],[[0,0],[0,0]],[[-57154,-1804],[-1804,0]],[[0,0],[0,0]],[[-13038,-1968],[-1968,0]],[[0,0],[0,0]],[[-738,-738],[-738,0]],[[0],[0,0]],[[0],[0,-82]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
