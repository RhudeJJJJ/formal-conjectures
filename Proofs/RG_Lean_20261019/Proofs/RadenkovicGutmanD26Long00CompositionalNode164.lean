/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode119
import Proofs.RadenkovicGutmanD26Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-712,0],[0,0]],[[0,0],[0,0]],[[-4400,0],[0,0]],[[0,0],[0,0]],[[-14664,0],[0,0]],[[0,0],[0,0]],[[-28528,0],[0,0]],[[0,0],[0,0]],[[-32736,-48],[-48,0]],[[0,0],[0,0]],[[-21008,-384],[-384,0]],[[0,0],[0,0]],[[-5896,-1056],[-1056,0]],[[0,0],[0,0]],[[480,-1152],[-1152,0]],[[0,0],[0,0]],[[504,-432],[-432,0]],[[0],[0,0]],[[0],[0,-48]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
