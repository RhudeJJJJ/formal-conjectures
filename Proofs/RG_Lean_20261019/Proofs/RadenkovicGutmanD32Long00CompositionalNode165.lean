/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode164
import Proofs.RadenkovicGutmanD32Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-60],[0]],[[0,0],[0]],[[-892,0],[0,0]],[[0,0],[0,0]],[[-5528,0],[0,0]],[[0,0],[0,0]],[[-18492,0],[0,0]],[[0,0],[0,0]],[[-36160,0],[0,0]],[[0,0],[0,0]],[[-41808,-60],[-60,0]],[[0,0],[0,0]],[[-27176,-480],[-480,0]],[[0,0],[0,0]],[[-7900,-1320],[-1320,0]],[[0,0],[0,0]],[[444,-1440],[-1440,0]],[[0,0],[0,0]],[[612,-540],[-540,0]],[[0],[0,0]],[[0],[0,-60]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
