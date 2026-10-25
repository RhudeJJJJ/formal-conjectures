/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode119
import Proofs.RadenkovicGutmanD38Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1072,0],[0,0]],[[0,0],[0,0]],[[-6656,0],[0,0]],[[0,0],[0,0]],[[-22320,0],[0,0]],[[0,0],[0,0]],[[-43792,0],[0,0]],[[0,0],[0,0]],[[-50880,-72],[-72,0]],[[0,0],[0,0]],[[-33344,-576],[-576,0]],[[0,0],[0,0]],[[-9904,-1584],[-1584,0]],[[0,0],[0,0]],[[408,-1728],[-1728,0]],[[0,0],[0,0]],[[720,-648],[-648,0]],[[0],[0,0]],[[0],[0,-72]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
