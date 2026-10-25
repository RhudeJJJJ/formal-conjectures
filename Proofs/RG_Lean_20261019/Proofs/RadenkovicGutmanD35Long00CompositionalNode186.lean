/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode178
import Proofs.RadenkovicGutmanD35Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-66],[0]],[[0,0],[0]],[[-1087,0],[0,0]],[[0,0],[0,0]],[[-7492,0],[0,0]],[[0,0],[0,0]],[[-28001,0],[0,0]],[[0,0],[0,0]],[[-61396,0],[0,0]],[[0,0],[0,0]],[[-79524,-66],[-66,0]],[[0,0],[0,0]],[[-57420,-493],[-493,0]],[[0,0],[0,0]],[[-18737,-1207],[-1207,0]],[[0,0],[0,0]],[[6,-1024],[-1024,0]],[[0,0],[0,0]],[[981,-139],[-139,0]],[[0,0],[0,0]],[[0,105],[105,-66]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
