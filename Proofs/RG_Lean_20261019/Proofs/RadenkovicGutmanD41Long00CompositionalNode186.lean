/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode178
import Proofs.RadenkovicGutmanD41Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-78],[0]],[[0,0],[0]],[[-1285,0],[0,0]],[[0,0],[0,0]],[[-8860,0],[0,0]],[[0,0],[0,0]],[[-33131,0],[0,0]],[[0,0],[0,0]],[[-72700,0],[0,0]],[[0,0],[0,0]],[[-94284,-78],[-78,0]],[[0,0],[0,0]],[[-68244,-583],[-583,0]],[[0,0],[0,0]],[[-22427,-1429],[-1429,0]],[[0,0],[0,0]],[[-102,-1216],[-1216,0]],[[0,0],[0,0]],[[1143,-169],[-169,0]],[[0,0],[0,0]],[[0,123],[123,-78]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
