/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode178
import Proofs.RadenkovicGutmanD24Long00CompositionalNode185
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e186 : NestedArithmetic.Expr 3 := .plus e178 e185
noncomputable def p186 : NestedHorner.Poly 3 := [[[-44],[0]],[[0,0],[0]],[[-724,0],[0,0]],[[0,0],[0,0]],[[-4984,0],[0,0]],[[0,0],[0,0]],[[-18596,0],[0,0]],[[0,0],[0,0]],[[-40672,0],[0,0]],[[0,0],[0,0]],[[-52464,-44],[-44,0]],[[0,0],[0,0]],[[-37576,-328],[-328,0]],[[0,0],[0,0]],[[-11972,-800],[-800,0]],[[0,0],[0,0]],[[204,-672],[-672,0]],[[0,0],[0,0]],[[684,-84],[-84,0]],[[0,0],[0,0]],[[0,72],[72,-44]]]
theorem step186 : p186=NestedHorner.add p178 p185 := by decide +kernel
#print axioms step186
theorem h186 : NestedArithmetic.compile e186=p186 := StagedExprCompile.compile_plus e186 e178 e185 p178 p185 p186 rfl h178 h185 step186
#print axioms h186
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
