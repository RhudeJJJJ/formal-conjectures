/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode036
import Proofs.RadenkovicGutmanD33Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-62]],[[0,0],[0]],[[630,-558],[-558]],[[0,0],[0]],[[438,-1488],[-1488]],[[0,0],[0]],[[-8234,-1364],[-1364]],[[0,0],[0]],[[-28204,-496],[-496]],[[0,0],[0]],[[-43320,-62],[-62]],[[0]],[[-37432]],[[0]],[[-19130]],[[0]],[[-5716]],[[0]],[[-922]],[[0]],[[-62]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
