/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode178
import Proofs.RadenkovicGutmanD14Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-24],[0]],[[0,0],[0]],[[-394,0],[0,0]],[[0,0],[0,0]],[[-2704,0],[0,0]],[[0,0],[0,0]],[[-10046,0],[0,0]],[[0,0],[0,0]],[[-21832,0],[0,0]],[[0,0],[0,0]],[[-27864,-24],[-24,0]],[[0,0],[0,0]],[[-19536,-178],[-178,0]],[[0,0],[0,0]],[[-5822,-430],[-430,0]],[[0,0],[0,0]],[[384,-352],[-352,0]],[[0,0],[0,0]],[[414,-34],[-34,0]],[[0,0],[0,0]],[[0,42],[42,-24]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
