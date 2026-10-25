/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode177
import Proofs.RadenkovicGutmanD13Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e178 : NestedArithmetic.Expr 3 := .times e177 e122
noncomputable def p178 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-374,0],[0,0]],[[0,0],[0,0]],[[-2684,0],[0,0]],[[0,0],[0,0]],[[-10582,0],[0,0]],[[0,0],[0,0]],[[-24992,0],[0,0]],[[0,0],[0,0]],[[-36168,-22],[-22,0]],[[0,0],[0,0]],[[-31460,-176],[-176,0]],[[0,0],[0,0]],[[-15334,-484],[-484,0]],[[0,0],[0,0]],[[-3498,-528],[-528,0]],[[0,0],[0,0]],[[-198,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step178 : p178=NestedArithmetic.mul p177 p122 := by decide +kernel
#print axioms step178
theorem h178 : NestedArithmetic.compile e178=p178 := StagedExprCompile.compile_times e178 e177 e122 p177 p122 p178 rfl h177 h122 step178
#print axioms h178
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
