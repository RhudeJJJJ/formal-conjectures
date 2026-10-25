/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode177
import Proofs.RadenkovicGutmanD20Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-36],[0]],[[0,0],[0]],[[-612,0],[0,0]],[[0,0],[0,0]],[[-4392,0],[0,0]],[[0,0],[0,0]],[[-17316,0],[0,0]],[[0,0],[0,0]],[[-40896,0],[0,0]],[[0,0],[0,0]],[[-59184,-36],[-36,0]],[[0,0],[0,0]],[[-51480,-288],[-288,0]],[[0,0],[0,0]],[[-25092,-792],[-792,0]],[[0,0],[0,0]],[[-5724,-864],[-864,0]],[[0,0],[0,0]],[[-324,-324],[-324,0]],[[0],[0,0]],[[0],[0,-36]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
