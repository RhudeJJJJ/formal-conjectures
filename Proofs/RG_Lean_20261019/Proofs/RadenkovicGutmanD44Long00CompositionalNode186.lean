/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode178
import Proofs.RadenkovicGutmanD44Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-84],[0]],[[0,0],[0]],[[-1384,0],[0,0]],[[0,0],[0,0]],[[-9544,0],[0,0]],[[0,0],[0,0]],[[-35696,0],[0,0]],[[0,0],[0,0]],[[-78352,0],[0,0]],[[0,0],[0,0]],[[-101664,-84],[-84,0]],[[0,0],[0,0]],[[-73656,-628],[-628,0]],[[0,0],[0,0]],[[-24272,-1540],[-1540,0]],[[0,0],[0,0]],[[-156,-1312],[-1312,0]],[[0,0],[0,0]],[[1224,-184],[-184,0]],[[0,0],[0,0]],[[0,132],[132,-84]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
