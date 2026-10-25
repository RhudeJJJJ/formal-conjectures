/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode164
import Proofs.RadenkovicGutmanD18Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e165 : NestedArithmetic.Expr 3 := .times e164 e122
noncomputable def p165 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-472,0],[0,0]],[[0,0],[0,0]],[[-2896,0],[0,0]],[[0,0],[0,0]],[[-9560,0],[0,0]],[[0,0],[0,0]],[[-18352,0],[0,0]],[[0,0],[0,0]],[[-20640,-32],[-32,0]],[[0,0],[0,0]],[[-12784,-256],[-256,0]],[[0,0],[0,0]],[[-3224,-704],[-704,0]],[[0,0],[0,0]],[[528,-768],[-768,0]],[[0,0],[0,0]],[[360,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step165 : p165=NestedArithmetic.mul p164 p122 := by decide +kernel
#print axioms step165
theorem h165 : NestedArithmetic.compile e165=p165 := StagedExprCompile.compile_times e165 e164 e122 p164 p122 p165 rfl h164 h122 step165
#print axioms h165
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
