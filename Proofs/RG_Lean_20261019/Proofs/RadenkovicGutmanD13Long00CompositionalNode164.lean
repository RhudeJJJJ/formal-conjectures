/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode119
import Proofs.RadenkovicGutmanD13Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-22],[0]],[[0,0],[0]],[[-322,0],[0,0]],[[0,0],[0,0]],[[-1956,0],[0,0]],[[0,0],[0,0]],[[-6370,0],[0,0]],[[0,0],[0,0]],[[-11992,0],[0,0]],[[0,0],[0,0]],[[-13080,-22],[-22,0]],[[0,0],[0,0]],[[-7644,-176],[-176,0]],[[0,0],[0,0]],[[-1554,-484],[-484,0]],[[0,0],[0,0]],[[558,-528],[-528,0]],[[0,0],[0,0]],[[270,-198],[-198,0]],[[0],[0,0]],[[0],[0,-22]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
