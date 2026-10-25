/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode036
import Proofs.RadenkovicGutmanD25Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-46]],[[0,0],[0]],[[486,-414],[-414]],[[0,0],[0]],[[486,-1104],[-1104]],[[0,0],[0]],[[-5562,-1012],[-1012]],[[0,0],[0]],[[-19980,-368],[-368]],[[0,0],[0]],[[-31224,-46],[-46]],[[0]],[[-27256]],[[0]],[[-14026]],[[0]],[[-4212]],[[0]],[[-682]],[[0]],[[-46]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
