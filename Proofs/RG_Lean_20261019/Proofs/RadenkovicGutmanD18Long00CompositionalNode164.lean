/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode119
import Proofs.RadenkovicGutmanD18Long00CompositionalNode163
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e164 : NestedArithmetic.Expr 3 := .times e119 e163
noncomputable def p164 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-472,0],[0,0]],[[0,0],[0,0]],[[-2896,0],[0,0]],[[0,0],[0,0]],[[-9560,0],[0,0]],[[0,0],[0,0]],[[-18352,0],[0,0]],[[0,0],[0,0]],[[-20640,-32],[-32,0]],[[0,0],[0,0]],[[-12784,-256],[-256,0]],[[0,0],[0,0]],[[-3224,-704],[-704,0]],[[0,0],[0,0]],[[528,-768],[-768,0]],[[0,0],[0,0]],[[360,-288],[-288,0]],[[0],[0,0]],[[0],[0,-32]]]
theorem step164 : p164=NestedArithmetic.mul p119 p163 := by decide +kernel
#print axioms step164
theorem h164 : NestedArithmetic.compile e164=p164 := StagedExprCompile.compile_times e164 e119 e163 p119 p163 p164 rfl h119 h163 step164
#print axioms h164
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
