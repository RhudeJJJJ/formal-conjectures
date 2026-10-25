/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode178
import Proofs.RadenkovicGutmanD22Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-658,0],[0,0]],[[0,0],[0,0]],[[-4528,0],[0,0]],[[0,0],[0,0]],[[-16886,0],[0,0]],[[0,0],[0,0]],[[-36904,0],[0,0]],[[0,0],[0,0]],[[-47544,-40],[-40,0]],[[0,0],[0,0]],[[-33968,-298],[-298,0]],[[0,0],[0,0]],[[-10742,-726],[-726,0]],[[0,0],[0,0]],[[240,-608],[-608,0]],[[0,0],[0,0]],[[630,-74],[-74,0]],[[0,0],[0,0]],[[0,66],[66,-40]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
