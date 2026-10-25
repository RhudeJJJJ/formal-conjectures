/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode174
import Proofs.RadenkovicGutmanD20Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-612,0],[0,0]],[[0,0],[0,0]],[[-4392,0],[0,0]],[[0,0],[0,0]],[[-17316,0],[0,0]],[[0,0],[0,0]],[[-40896,0],[0,0]],[[0,0],[0,0]],[[-59184,-36],[-36,0]],[[0,0],[0,0]],[[-51480,-288],[-288,0]],[[0,0],[0,0]],[[-25092,-792],[-792,0]],[[0,0],[0,0]],[[-5724,-864],[-864,0]],[[0,0],[0,0]],[[-324,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
