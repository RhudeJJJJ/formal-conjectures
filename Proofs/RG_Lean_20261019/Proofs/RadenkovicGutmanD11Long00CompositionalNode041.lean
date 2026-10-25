/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode036
import Proofs.RadenkovicGutmanD11Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-18]],[[0,0],[0]],[[234,-162],[-162]],[[0,0],[0]],[[570,-432],[-432]],[[0,0],[0]],[[-886,-396],[-396]],[[0,0],[0]],[[-5588,-144],[-144]],[[0,0],[0]],[[-10056,-18],[-18]],[[0]],[[-9448]],[[0]],[[-5094]],[[0]],[[-1580]],[[0]],[[-262]],[[0]],[[-18]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
