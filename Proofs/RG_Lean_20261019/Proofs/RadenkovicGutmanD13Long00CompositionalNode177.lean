/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode174
import Proofs.RadenkovicGutmanD13Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e177 : NestedArithmetic.Expr 3 := .times e174 e176
noncomputable def p177 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-374,0],[0,0]],[[0,0],[0,0]],[[-2684,0],[0,0]],[[0,0],[0,0]],[[-10582,0],[0,0]],[[0,0],[0,0]],[[-24992,0],[0,0]],[[0,0],[0,0]],[[-36168,-22],[-22,0]],[[0,0],[0,0]],[[-31460,-176],[-176,0]],[[0,0],[0,0]],[[-15334,-484],[-484,0]],[[0,0],[0,0]],[[-3498,-528],[-528,0]],[[0,0],[0,0]],[[-198,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step177 : p177=NestedArithmetic.mul p174 p176 := by decide +kernel
#print axioms step177
theorem h177 : NestedArithmetic.compile e177=p177 := StagedExprCompile.compile_times e177 e174 e176 p174 p176 p177 rfl h174 h176 step177
#print axioms h177
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
