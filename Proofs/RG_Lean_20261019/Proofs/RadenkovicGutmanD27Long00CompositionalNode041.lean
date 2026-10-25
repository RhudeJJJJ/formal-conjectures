/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode036
import Proofs.RadenkovicGutmanD27Long00CompositionalNode040
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e041 : NestedArithmetic.Expr 3 := .times e036 e040
noncomputable def p041 : NestedHorner.Poly 3 := [[[],[]],[[0],[0,-50]],[[0,0],[0]],[[522,-450],[-450]],[[0,0],[0]],[[474,-1200],[-1200]],[[0,0],[0]],[[-6230,-1100],[-1100]],[[0,0],[0]],[[-22036,-400],[-400]],[[0,0],[0]],[[-34248,-50],[-50]],[[0]],[[-29800]],[[0]],[[-15302]],[[0]],[[-4588]],[[0]],[[-742]],[[0]],[[-50]]]
theorem step041 : p041=NestedArithmetic.mul p036 p040 := by decide +kernel
#print axioms step041
theorem h041 : NestedArithmetic.compile e041=p041 := StagedExprCompile.compile_times e041 e036 e040 p036 p040 p041 rfl h036 h040 step041
#print axioms h041
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
