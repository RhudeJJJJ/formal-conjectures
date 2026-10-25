/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode119
import Proofs.RadenkovicGutmanD32Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-892,0],[0,0]],[[0,0],[0,0]],[[-5528,0],[0,0]],[[0,0],[0,0]],[[-18492,0],[0,0]],[[0,0],[0,0]],[[-36160,0],[0,0]],[[0,0],[0,0]],[[-41808,-60],[-60,0]],[[0,0],[0,0]],[[-27176,-480],[-480,0]],[[0,0],[0,0]],[[-7900,-1320],[-1320,0]],[[0,0],[0,0]],[[444,-1440],[-1440,0]],[[0,0],[0,0]],[[612,-540],[-540,0]],[[0],[0,0]],[[0],[0,-60]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
