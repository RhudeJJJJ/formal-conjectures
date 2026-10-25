/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode073
import Proofs.RadenkovicGutmanD7Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-504,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4536,-15120,0],[-15120,-6258,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-295218,-206010,0],[-206010,-31220,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4061610,-1207836,0],[-1207836,-81298,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27373920,-4025630,0],[-4025630,-121044,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-112341026,-8513708,0],[-8513708,-107240,0],[0,0]],[[0,0,0],[0,0],[0]],[[-310206078,-12101726,0],[-12101726,-57036],[0]],[[0,0,0],[0,0],[0]],[[-609731500,-11946312,0],[-11946312,-17794],[0]],[[0,0,0],[0,0],[0]],[[-883515360,-8333052,0],[-8333052,-2996],[0]],[[0,0,0],[0,0],[0]],[[-965301806,-4128376,0],[-4128376,-210],[0]],[[0,0,0],[0,0],[0]],[[-806537228,-1441958,0],[-1441958,0],[0]],[[0,0],[0]],[[-519336860,-346780],[-346780]],[[0,0],[0]],[[-258254920,-54614],[-54614]],[[0,0],[0]],[[-98824446,-5068],[-5068]],[[0,0],[0]],[[-28803558,-210],[-210]],[[0,0],[0]],[[-6272700,0],[0]],[[0]],[[-987560]],[[0]],[[-106106]],[[0]],[[-6958]],[[0]],[[-210]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
