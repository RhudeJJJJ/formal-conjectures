/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode119
import Proofs.RadenkovicGutmanD12Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-20],[0]],[[0,0],[0]],[[-292,0],[0,0]],[[0,0],[0,0]],[[-1768,0],[0,0]],[[0,0],[0,0]],[[-5732,0],[0,0]],[[0,0],[0,0]],[[-10720,0],[0,0]],[[0,0],[0,0]],[[-11568,-20],[-20,0]],[[0,0],[0,0]],[[-6616,-160],[-160,0]],[[0,0],[0,0]],[[-1220,-440],[-440,0]],[[0,0],[0,0]],[[564,-480],[-480,0]],[[0,0],[0,0]],[[252,-180],[-180,0]],[[0],[0,0]],[[0],[0,-20]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
