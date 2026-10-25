/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode036
import Proofs.RadenkovicGutmanD9Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-14]],[[0,0],[0]],[[198,-126],[-126]],[[0,0],[0]],[[582,-336],[-336]],[[0,0],[0]],[[-218,-308],[-308]],[[0,0],[0]],[[-3532,-112],[-112]],[[0,0],[0]],[[-7032,-14],[-14]],[[0]],[[-6904]],[[0]],[[-3818]],[[0]],[[-1204]],[[0]],[[-202]],[[0]],[[-14]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
