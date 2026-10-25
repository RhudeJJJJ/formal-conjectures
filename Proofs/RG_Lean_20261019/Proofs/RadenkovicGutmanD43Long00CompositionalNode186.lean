/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode178
import Proofs.RadenkovicGutmanD43Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-82],[0]],[[0,0],[0]],[[-1351,0],[0,0]],[[0,0],[0,0]],[[-9316,0],[0,0]],[[0,0],[0,0]],[[-34841,0],[0,0]],[[0,0],[0,0]],[[-76468,0],[0,0]],[[0,0],[0,0]],[[-99204,-82],[-82,0]],[[0,0],[0,0]],[[-71852,-613],[-613,0]],[[0,0],[0,0]],[[-23657,-1503],[-1503,0]],[[0,0],[0,0]],[[-138,-1280],[-1280,0]],[[0,0],[0,0]],[[1197,-179],[-179,0]],[[0,0],[0,0]],[[0,129],[129,-82]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
