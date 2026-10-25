/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode164
import Proofs.RadenkovicGutmanD38Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1072,0],[0,0]],[[0,0],[0,0]],[[-6656,0],[0,0]],[[0,0],[0,0]],[[-22320,0],[0,0]],[[0,0],[0,0]],[[-43792,0],[0,0]],[[0,0],[0,0]],[[-50880,-72],[-72,0]],[[0,0],[0,0]],[[-33344,-576],[-576,0]],[[0,0],[0,0]],[[-9904,-1584],[-1584,0]],[[0,0],[0,0]],[[408,-1728],[-1728,0]],[[0,0],[0,0]],[[720,-648],[-648,0]],[[0],[0,0]],[[0],[0,-72]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
