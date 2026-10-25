/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode178
import Proofs.RadenkovicGutmanD9Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-14],[0]],[[0,0],[0]],[[-229,0],[0,0]],[[0,0],[0,0]],[[-1564,0],[0,0]],[[0,0],[0,0]],[[-5771,0],[0,0]],[[0,0],[0,0]],[[-12412,0],[0,0]],[[0,0],[0,0]],[[-15564,-14],[-14,0]],[[0,0],[0,0]],[[-10516,-103],[-103,0]],[[0,0],[0,0]],[[-2747,-245],[-245,0]],[[0,0],[0,0]],[[474,-192],[-192,0]],[[0,0],[0,0]],[[279,-9],[-9,0]],[[0,0],[0,0]],[[0,27],[27,-14]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
