/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode036
import Proofs.RadenkovicGutmanD19Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-34]],[[0,0],[0]],[[378,-306],[-306]],[[0,0],[0]],[[522,-816],[-816]],[[0,0],[0]],[[-3558,-748],[-748]],[[0,0],[0]],[[-13812,-272],[-272]],[[0,0],[0]],[[-22152,-34],[-34]],[[0]],[[-19624]],[[0]],[[-10198]],[[0]],[[-3084]],[[0]],[[-502]],[[0]],[[-34]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
