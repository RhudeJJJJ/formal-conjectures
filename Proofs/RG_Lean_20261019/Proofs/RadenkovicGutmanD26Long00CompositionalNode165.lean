/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode164
import Proofs.RadenkovicGutmanD26Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-712,0],[0,0]],[[0,0],[0,0]],[[-4400,0],[0,0]],[[0,0],[0,0]],[[-14664,0],[0,0]],[[0,0],[0,0]],[[-28528,0],[0,0]],[[0,0],[0,0]],[[-32736,-48],[-48,0]],[[0,0],[0,0]],[[-21008,-384],[-384,0]],[[0,0],[0,0]],[[-5896,-1056],[-1056,0]],[[0,0],[0,0]],[[480,-1152],[-1152,0]],[[0,0],[0,0]],[[504,-432],[-432,0]],[[0],[0,0]],[[0],[0,-48]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
