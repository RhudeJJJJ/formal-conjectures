/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode178
import Proofs.RadenkovicGutmanD19Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-34],[0]],[[0,0],[0]],[[-559,0],[0,0]],[[0,0],[0,0]],[[-3844,0],[0,0]],[[0,0],[0,0]],[[-14321,0],[0,0]],[[0,0],[0,0]],[[-31252,0],[0,0]],[[0,0],[0,0]],[[-40164,-34],[-34,0]],[[0,0],[0,0]],[[-28556,-253],[-253,0]],[[0,0],[0,0]],[[-8897,-615],[-615,0]],[[0,0],[0,0]],[[294,-512],[-512,0]],[[0,0],[0,0]],[[549,-59],[-59,0]],[[0,0],[0,0]],[[0,57],[57,-34]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
