/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode178
import Proofs.RadenkovicGutmanD7Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-10],[0]],[[0,0],[0]],[[-163,0],[0,0]],[[0,0],[0,0]],[[-1108,0],[0,0]],[[0,0],[0,0]],[[-4061,0],[0,0]],[[0,0],[0,0]],[[-8644,0],[0,0]],[[0,0],[0,0]],[[-10644,-10],[-10,0]],[[0,0],[0,0]],[[-6908,-73],[-73,0]],[[0,0],[0,0]],[[-1517,-171],[-171,0]],[[0,0],[0,0]],[[510,-128],[-128,0]],[[0,0],[0,0]],[[225,1],[1,0]],[[0,0],[0,0]],[[0,21],[21,-10]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
