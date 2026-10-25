/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode073
import Proofs.RadenkovicGutmanD42Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-3024,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27216,-408240,0],[-408240,-90468,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7010388,-5840100,0],[-5840100,-645960,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-109941300,-35612136,0],[-35612136,-2045988,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-785947680,-122437980,0],[-122437980,-3419304,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3345006756,-265302408,0],[-265302408,-3254160,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9476594988,-384350316,0],[-384350316,-1812216],[0]],[[0,0,0],[0,0],[0]],[[-18992100120,-385175952,0],[-385175952,-583044],[0]],[[0,0,0],[0,0],[0]],[[-27945654240,-271956552,0],[-271956552,-100296],[0]],[[0,0,0],[0,0],[0]],[[-30916692156,-136078656,0],[-136078656,-7140],[0]],[[0,0,0],[0,0],[0]],[[-26102091288,-47924268,0],[-47924268,0],[0]],[[0,0],[0]],[[-16956188760,-11606280],[-11606280]],[[0,0],[0]],[[-8495973360,-1838844],[-1838844]],[[0,0],[0]],[[-3272503836,-171528],[-171528]],[[0,0],[0]],[[-959312508,-7140],[-7140]],[[0,0],[0]],[[-209979000,0],[0]],[[0]],[[-33208560]],[[0]],[[-3582516]],[[0]],[[-235788]],[[0]],[[-7140]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
