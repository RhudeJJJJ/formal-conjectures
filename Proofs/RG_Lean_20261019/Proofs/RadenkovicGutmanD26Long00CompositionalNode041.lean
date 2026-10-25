/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode036
import Proofs.RadenkovicGutmanD26Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-48]],[[0,0],[0]],[[504,-432],[-432]],[[0,0],[0]],[[480,-1152],[-1152]],[[0,0],[0]],[[-5896,-1056],[-1056]],[[0,0],[0]],[[-21008,-384],[-384]],[[0,0],[0]],[[-32736,-48],[-48]],[[0]],[[-28528]],[[0]],[[-14664]],[[0]],[[-4400]],[[0]],[[-712]],[[0]],[[-48]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
