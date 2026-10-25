/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode059
import Proofs.RadenkovicGutmanD43Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,129],[129,-82]],[[0,0],[0]],[[1197,-179],[-179]],[[0,0],[0]],[[-138,-1280],[-1280]],[[0,0],[0]],[[-23657,-1503],[-1503]],[[0,0],[0]],[[-71852,-613],[-613]],[[0,0],[0]],[[-99204,-82],[-82]],[[0]],[[-76468]],[[0]],[[-34841]],[[0]],[[-9316]],[[0]],[[-1351]],[[0]],[[-82]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
