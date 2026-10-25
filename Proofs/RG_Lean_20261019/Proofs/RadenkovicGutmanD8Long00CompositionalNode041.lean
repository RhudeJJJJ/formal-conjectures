/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode036
import Proofs.RadenkovicGutmanD8Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-12]],[[0,0],[0]],[[180,-108],[-108]],[[0,0],[0]],[[588,-288],[-288]],[[0,0],[0]],[[116,-264],[-264]],[[0,0],[0]],[[-2504,-96],[-96]],[[0,0],[0]],[[-5520,-12],[-12]],[[0]],[[-5632]],[[0]],[[-3180]],[[0]],[[-1016]],[[0]],[[-172]],[[0]],[[-12]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
