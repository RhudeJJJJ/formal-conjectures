/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode036
import Proofs.RadenkovicGutmanD18Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-32]],[[0,0],[0]],[[360,-288],[-288]],[[0,0],[0]],[[528,-768],[-768]],[[0,0],[0]],[[-3224,-704],[-704]],[[0,0],[0]],[[-12784,-256],[-256]],[[0,0],[0]],[[-20640,-32],[-32]],[[0]],[[-18352]],[[0]],[[-9560]],[[0]],[[-2896]],[[0]],[[-472]],[[0]],[[-32]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
